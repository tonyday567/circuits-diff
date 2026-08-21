{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
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

import Circuit.Body (Body (..))
import Circuit.Dagger (CopyT (..), DiscardT (..), MergeT (..), ZeroT (..))
import Circuit.Diff (Diff (..), Diff', runDiff)
import Circuit.Diff.Circuit ()
import Circuit.Diff.Pullback (Pullback (..))
import Circuit.Net (Net (..), lift)
import Circuit.SMC (SMC (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category ((.))
-- >>> import Circuit.Diff
-- >>> import Circuit.Dagger qualified as CD
-- >>> import Circuit.Net (Net (..), lift)
-- >>> import Circuit.Diff.Pullback (Pullback (..), evalPullback)
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
-- Use 'Circuit.Diff.Pullback.evalPullback' to evaluate the resulting net
-- at a single output cotangent.
--
-- >>> let sq = Diff (\x -> (x * x, \d -> 2 * x * d))
-- >>> let n = Plus . Par (lift sq) (lift sq) . Copy :: Net (,) Diff' Double Double
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
-- Structural rows ('Copy', 'Plus', 'Discard', 'Zero') are converted to
-- point-independent 'lift' pullbacks using the 'Diff' dictionaries the
-- constructors already carry (copy↦plus, plus↦dup, discard↦zero,
-- zero↦discard).
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
  FromSMC s -> linearizeSMC s a
  Compose g f ->
    let (b, f') = linearizeNet f a
        (c, g') = linearizeNet g b
     in (c, Compose f' g')
  Par f g ->
    let (a1, a2) = a
        (b, f') = linearizeNet f a1
        (d, g') = linearizeNet g a2
     in ((b, d), Par f' g')
  Copy ->
    let (out, pb) = runDiff (copyT :: Diff p a (a, a)) a
     in (out, lift (Pullback pb))
  Discard ->
    let (out, pb) = runDiff (discardT @(,) :: Diff p a ()) a
     in (out, lift (Pullback pb))
  Plus ->
    let (out, pb) = runDiff (plusT :: Diff p (b, b) b) a
     in (out, lift (Pullback pb))
  Zero ->
    let (out, pb) = runDiff (zeroT @(,) :: Diff p () b) ()
     in (out, lift (Pullback pb))
  where
    linearizeSMC ::
      forall x y.
      SMC (,) (Diff p) x y ->
      x ->
      (y, Net (,) Pullback y x)
    linearizeSMC s x = case s of
      SMCLift d ->
        let (y, pb) = runDiff d x
         in (y, lift (Pullback pb))
      SMCCompose g f ->
        let (b, f') = linearizeSMC f x
            (c, g') = linearizeSMC g b
         in (c, Compose f' g')
      SMCPar f g ->
        let (x1, x2) = x
            (b, f') = linearizeSMC f x1
            (d, g') = linearizeSMC g x2
         in ((b, d), Par f' g')
      SMCSwap ->
        let (u, v) = x
         in ((v, u), FromSMC SMCSwap)

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
  Body (,) (Diff p) s a b ->
  a ->
  (b, Body (,) Pullback s b a)
linearizeBody (Body f) a =
  let ~((s, b), pb) = runDiff f (s, a)
   in (b, Body (Pullback pb))
