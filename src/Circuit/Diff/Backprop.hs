{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Pointwise linearization and backpropagation for 'Diff' nets and bodies.
--
-- 'linearizeAt' runs a 'Net (,) (Diff p)' forward at a primal point and builds
-- the transposed net of pointwise pullbacks.  This is the honest reverse-mode
-- gradient net: the graph's structure is burned down into a straight linear
-- (affine) cotangent map.
--
-- For feedback-bearing circuits, use 'linearizeBody' on a 'Body' value.
-- The channel type stays exposed, so star-elimination can operate without
-- recovering evidence from a hidden 'Loop.Knot'.
module Circuit.Diff.Backprop
  ( -- * Pointwise linearization
    linearizeAt,
    fromDiffAt,

    -- * Linearization over the body language
    linearizeBody,
  )
where

import Circuit.Bimonoid
  ( CopyT (..),
    DiscardT (..),
    MergeT (..),
    SigCopy (..),
    SigDiscard (..),
    SigPlus (..),
    SigZero (..),
    ZeroT (..),
  )
import Circuit.Body (Body (..))
import Circuit.Category ((.))
import Circuit.Diff (Diff (..), Diff', runDiff)
import Circuit.Diff.Circuit ()
import Circuit.Net (Net, widen)
import Circuit.Pullback (Pullback (..))
import Circuit.SMC (SMC, SigPar (..), SigSwap (..))
import Circuit.SMC qualified as SMC
import Circuit.Syntax (SigCompose (..), Syntax (..), (:+:) (..))
import Circuit.Tensor (Tensor (..))
import NumHask.Prelude hiding ((.))

-- $setup
-- >>> import Circuit.Category ((.))
-- >>> import Circuit.Diff
-- >>> import Circuit.Bimonoid qualified as Bm
-- >>> import Circuit.Net (Net, lift, widen)
-- >>> import Circuit.Pullback (Pullback (..), evalPullback)
-- >>> import Circuit.SMC qualified as SMC
-- >>> import Circuit.Tensor (Tensor (..))
-- >>> import Prelude hiding (id, (.))

-- | Pointwise linearization: run a 'Net' of 'Diff' primitives forward at @a@
-- and build the transposed net of pullbacks.
--
-- This is the same operation as /backpropagation/, but read forwards
-- through the lens of 'linearize': the graph's structure is burned down
-- into a straight linear (affine) cotangent map.  Looking backwards, the
-- single output cotangent appears to bifurcate and fan out through the
-- wiring.  Propagate fans values out in the forward direction; linearize
-- straightens them into a wire in the reverse direction.
--
-- This is the honest reverse-mode gradient net.  'transpose' alone is
-- only correct for linear nets; for nonlinear 'Diff' primitives the
-- pullback closure depends on the primal point.  'linearizeAt' runs
-- the net, captures each primitive's pullback at the point it saw,
-- and returns both the output value and a 'Net Pullback' whose wires
-- are those pointwise pullbacks composed in reverse order.
--
-- Use 'Circuit.Pullback.evalPullback' to evaluate the resulting net
-- at a single output cotangent.
--
-- >>> let sq = Diff (\x -> (x * x, \d -> 2 * x * d)) :: Diff' Double Double
-- >>> let copyN = lift (Bm.copyT @(,) @Diff' @Double) :: Net (,) Diff' Double (Double, Double)
-- >>> let plusN = lift (Bm.plusT @(,) @Diff' @Double) :: Net (,) Diff' (Double, Double) Double
-- >>> let parN = widen (tensor (SMC.lift sq) (SMC.lift sq)) :: Net (,) Diff' (Double, Double) (Double, Double)
-- >>> let n = plusN . parN . copyN :: Net (,) Diff' Double Double
-- >>> let (y, g) = linearizeAt n 3.0
-- >>> y
-- 18.0
-- >>> evalPullback g 1.0
-- 12.0

-- | Capture the pullback of a 'Diff' primitive at a primal point.
--
-- >>> let d = Diff (\x -> (x * x, \dy -> 2 * x * dy))
-- >>> runPullback (fromDiffAt d 3) 1
-- 6
fromDiffAt :: forall p a b. Diff p a b -> a -> Pullback b a
fromDiffAt (Diff f) a = Pullback (snd (f a))
{-# INLINE fromDiffAt #-}

-- | Run a 'Net' of 'Diff' primitives forward and build the transposed
-- pullback net.
--
-- Structural rows ('SigCopy', 'SigPlus', 'SigDiscard', 'SigZero') are
-- converted to point-independent 'lift' pullbacks using the 'Diff'
-- dictionaries the constructors already carry (copy↦plus, plus↦dup,
-- discard↦zero, zero↦discard).
linearizeAt ::
  forall p a b.
  Net (,) (Diff p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeAt = linearizeNet

-- | Pointwise linearization over the free 'Net' language.
linearizeNet ::
  forall p a b.
  Net (,) (Diff p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeNet n a = case n of
  Lift d ->
    let (y, pb) = runDiff d a
     in (y, Lift (Pullback pb))
  Oper op -> case op of
    L (SigCompose g f) ->
      let (b, f') = linearizeNet f a
          (c, g') = linearizeNet g b
       in (c, f' . g')
    R (L (SigPar f g)) ->
      let (a1, a2) = a
          (b, f') = linearizeNet f a1
          (d, g') = linearizeNet g a2
       in ((b, d), Oper (R (L (SigPar f' g'))))
    R (R (L SigSwap)) ->
      let (u, v) = a
       in ((v, u), Oper (R (R (L SigSwap))))
    R (R (R (L SigCopy))) ->
      let (out, pb) = runDiff (copyT @(,) @(Diff p)) a
       in (out, Lift (Pullback pb))
    R (R (R (R (L SigDiscard)))) ->
      let (out, pb) = runDiff (discardT @(,) @(Diff p)) a
       in (out, Lift (Pullback pb))
    R (R (R (R (R (L SigPlus))))) ->
      let (out, pb) = runDiff (plusT @(,) @(Diff p)) a
       in (out, Lift (Pullback pb))
    R (R (R (R (R (R SigZero))))) ->
      let (out, pb) = runDiff (zeroT @(,) @(Diff p)) ()
       in (out, Lift (Pullback pb))

-- | Pointwise linearization over the core 'Body' language.
--
-- The channel type @s@ stays exposed, so the result can be fed directly to
-- 'Circuit.Diff.Star.solveStarBody' without any coercion.
--
-- /Caveat/: fixpoints are lazy on both passes.  The forward body ties the
-- same lazy knot as 'Trace' @Diff@; the returned body ties the lazy
-- 'Trace' @Pullback@ knot.  For strict carriers with nonzero channel
-- self-coupling, /both/ diverge.  The backward side can be solved in closed
-- form by 'Circuit.Diff.Star.solveStarBody'.
linearizeBody ::
  forall p s a b.
  Body (,) s (Diff p) a b ->
  a ->
  (b, Body (,) s Pullback b a)
linearizeBody (Body f) a =
  let ~((s, b), pb) = runDiff f (s, a)
   in (b, Body (Pullback pb))
