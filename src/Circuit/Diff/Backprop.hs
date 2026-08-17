{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Pointwise linearization and backpropagation for 'Diff'' nets.
--
-- 'backprop' runs a 'Net (,) Diff' forward at a primal point and builds the
-- transposed net of pointwise pullbacks.  This is the honest reverse-mode
-- gradient net: the graph's structure is burned down into a straight linear
-- (affine) cotangent map.
module Circuit.Diff.Backprop
  ( -- * Inspectable backprop
    backprop,
    linearizeAt,
    fromDiffAt,

    -- * Linearization over net and loop languages
    linearizeNet,
    linearizeCircuit,
  )
where

import Circuit.Dagger (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Diff (Diff', runDiff, pattern Diff)
import Circuit.Diff.Circuit ()
import Circuit.Diff.Pullback (Pullback (..))
import Circuit.Loop qualified as C
import Circuit.Net (Net (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Diff
-- >>> import Circuit.Dagger qualified as CD
-- >>> import Circuit.Net (Net (..))
-- >>> import Circuit.Diff.Pullback (Pullback (..), evalPullback)
-- >>> import Prelude hiding (id, (.))

-- | Pointwise linearization: run a 'Net Diff' forward at @a@ and
-- build the transposed net of pullbacks.
--
-- This is the same operation as /backpropagation/, but read forwards
-- through the lens of 'linearize': the graph's structure is burned down
-- into a straight linear (affine) cotangent map.  'backprop' is the dual
-- view — looking backwards, the single output cotangent appears to
-- bifurcate and fan out through the wiring.  Propagate fans values out in
-- the forward direction; linearize straightens them into a wire in the
-- reverse direction.
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
-- __Caveat__: /Fixpoints are lazy on both passes./  Forward 'Trace's tie
-- the same lazy knot as 'Trace' @Diff@; the 'Trace's in the returned net
-- tie the lazy 'Trace' @Pullback@ knot.  For strict carriers with
-- nonzero channel self-coupling, /both/ diverge.  The forward side needs
-- an iteration policy (a @backpropNFrom@, mirroring 'traceNFrom').  The
-- backward side deserves better: the pullback net is linear by
-- construction, so its knots satisfy affine equations and can be
-- /eliminated/ — probe the knot body for its channel matrix,
-- 'Circuit.Mat.Dense.starMatrix' it, and replace the 'Trace' with a 'Lift'.
-- That elimination pass is state elimination on a linear circuit: the
-- linear-representation normal form that @kleeneSimplify@ gestures at,
-- landing where it can actually be lawful.
--
-- >>> let sq = Diff (\x -> (x * x, \d -> 2 * x * d))
-- >>> let n = Compose (Lift (CD.plus :: Diff (Double, Double) Double)) (Compose (Par (Lift sq) (Lift sq)) Copy) :: Net (,) Diff Double Double
-- >>> let (y, g) = backprop n 3.0
-- >>> y
-- 18.0
-- >>> evalPullback g 1.0
-- 12.0
backprop ::
  forall p a b.
  Net (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
backprop = linearizeAt

-- | Capture the pullback of a 'Diff' primitive at a primal point.
--
-- >>> let d = Diff (\x -> (x * x, \dy -> 2 * x * dy))
-- >>> runPullback (fromDiffAt d 3) 1
-- 6
fromDiffAt :: forall p a b. Diff' p a b -> a -> Pullback b a
fromDiffAt (Diff f) a = Pullback (snd (f a))
{-# INLINE fromDiffAt #-}

-- | Run a 'Net Diff' forward and build the transposed pullback net.
--
-- This linearizes the 'Net' directly, without 'Circuit.Net.melt', so
-- 'Trace's inside 'Par' arms survive as 'Trace's in the pullback net.
linearizeAt ::
  forall p a b.
  Net (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeAt = linearizeNet

-- | Pointwise linearization over the free 'Net' language.
--
-- 'Par' is preserved as 'Par'.  Structural rows ('Copy', 'Add',
-- 'Discard', 'Zero') are converted to point-independent 'Lift'
-- pullbacks using the 'Diff' dictionaries the constructors already
-- carry (copy↦plus, add↦dup, discard↦zero, zero↦discard).  Because the
-- recursion never melts the net into a 'Trace' first, feedback loops
-- under 'Par' remain visible to future star-elimination passes.
linearizeNet ::
  forall p a b.
  Net (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeNet n a = case n of
  Lift d ->
    let (b, pb) = runDiff d a
     in (b, Lift (Pullback pb))
  Compose g f ->
    let (b, f') = linearizeNet f a
        (c, g') = linearizeNet g b
     in (c, Compose f' g')
  Par f g ->
    let (a1, a2) = a
        (b, f') = linearizeNet f a1
        (d, g') = linearizeNet g a2
     in ((b, d), Par f' g')
  Swap ->
    let (x, y) = a
     in ((y, x), Swap)
  Copy ->
    let (out, pb) = runDiff (copy :: Diff' p a (a, a)) a
     in (out, Lift (Pullback pb))
  Discard ->
    let (out, pb) = runDiff (discard :: Diff' p a ()) a
     in (out, Lift (Pullback pb))
  Plus ->
    let (out, pb) = runDiff (plus :: Diff' p (b, b) b) a
     in (out, Lift (Pullback pb))
  Zero ->
    let (out, pb) = runDiff (zero :: Diff' p () b) ()
     in (out, Lift (Pullback pb))
  Knot f ->
    let ~((x, b), f') = linearizeNet f (x, a)
     in (b, Knot f')

-- | Pointwise linearization over the core 'Loop' language.  The
-- bimonoid rows ('Copy', 'Plus', ...) have already been melted into
-- 'Lift's by 'Circuit.Net.melt', so this recursion only sees 'Lift' and
-- 'Knot'.
linearizeCircuit ::
  forall p a b.
  C.Loop (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeCircuit (C.Lift (Diff f)) a =
  let (b, pb) = f a
   in (b, Lift (Pullback pb))
linearizeCircuit (C.Knot f) a =
  let ~((x, b), pb) = runDiff f (x, a)
   in (b, Knot (Lift (Pullback pb)))
