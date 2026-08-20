{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Star-elimination of @(,)@ knots in linear 'Pullback' nets.
--
-- A 'Net (,) (,) Pullback' built by 'Circuit.Diff.Backprop.linearizeAt' is linear by
-- construction: every 'Lift' is a pointwise pullback, every 'Compose' is
-- function composition, and every 'Trace' ties an affine feedback equation.
-- This module eliminates those knots in closed form using the Kleene star
-- ('NumHask.Algebra.Ring.StarSemiring' for scalar channels,
-- 'Circuit.Mat.Dense.starMatrix' for vector channels).
--
-- The pass is /structural/: it recurses through the net, replaces each
-- 'Trace' (innermost first — Bekić order) with a single solved 'Lift', and
-- leaves every other constructor in place.  The result preserves the net's
-- shape minus its loops, so it can be evaluated on strict carriers without
-- the lazy-knot divergence that 'Trace' @Pullback (,)@ suffers when channel
-- self-coupling is non-zero — and it remains inspectable: the only opaque
-- nodes are the ones Gaussian elimination genuinely created.
module Circuit.Diff.Eliminate
  ( -- * Channel abstraction
    StarChannel (..),

    -- * Structural melting
    melt,

    -- * Trace elimination
    eliminateKnots,
  )
where

import Circuit.Dagger (CopyT (..), DiscardT (..), MergeT (..), ZeroT (..))
import Circuit.Dagger qualified
import Circuit.Diff.Pullback (Pullback (..))
import Circuit.Layer (run)
import Circuit.Mat.Dense (Matrix (..), fromLists, matVec, starMatrix, toLists)
import Circuit.Net (Net (..))
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import NumHask.Free.Carriers (FieldStar (..))
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (id, (.))
import Prelude qualified as P

-- $setup
-- >>> import Circuit.Diff.Pullback (Pullback (..), evalPullback)
-- >>> import Circuit.Net (Net (..))
-- >>> import NumHask.Free.Carriers (FieldStar (..))
-- >>> import Prelude hiding (id, (.))

-- | Replace every structural row with its pure 'Pullback' interpretation.
--
-- 'Circuit.Net.melt' melts bimonoid rows ('Copy', 'Discard', 'Plus',
-- 'Zero') by /running/ the net.  That is fine for knot-free wiring, but it
-- eagerly ties any lazy 'Trace' encountered along the way — so a net with
-- non-zero channel self-coupling diverges before a subsequent star-elimination
-- pass can save it.
--
-- This pass performs the same row elimination /without/ running anything.
-- Each structural row is replaced by the corresponding 'Pullback' arrow,
-- lifted into a 'Net' node.  The result is semantically equivalent but
-- contains only 'Lift', 'Compose', 'Swap', 'Par' and 'Knot' constructors.
-- After melting, 'eliminateKnots' can remove the knots in closed form.
melt :: Net (,) (,) Pullback a b -> Net (,) (,) Pullback a b
melt = \case
  Lift p -> Lift p
  Compose g f -> Compose (melt g) (melt f)
  Par f g -> Par (melt f) (melt g)
  Swap -> Swap
  Knot f -> Knot (melt f)
  Copy -> Lift copyT
  Discard -> Lift (discardT @(,))
  Plus -> Lift plusT
  Zero -> Lift (zeroT @(,))

-- | Feedback channels that support star-elimination.
--
-- The class abstracts over scalar and vector channels.  For a scalar channel
-- the self-coupling is a single scalar; for a vector channel it is a matrix.
--
-- Channel arithmetic ('addChannel', 'negateChannel') is part of the class
-- rather than an @Additive (->) j@ constraint: only 'addChannel' is ever needed
-- (never a dimension-blind @zero ()@), and list channels could not lawfully
-- supply the latter.
class
  ( NHR.StarSemiring (Scalar j),
    NHA.Additive (Scalar j),
    NHM.Multiplicative (Scalar j)
  ) =>
  StarChannel j
  where
  -- | The scalar carrier of the channel (e.g. 'FieldStar' or the element
  -- type of a list).
  type Scalar j

  -- | Dimension of the channel cotangent space, read off a witness value.
  channelDim :: j -> Int

  -- | Zero channel cotangent of the given dimension.
  zeroChannel :: Int -> j

  -- | Basis vector @e_i@: @basisChannel dim i@.
  basisChannel :: Int -> Int -> j

  -- | Componentwise sum of two (full-length) channel cotangents.
  addChannel :: j -> j -> j

  -- | Additive inverse of a channel cotangent.
  negateChannel :: j -> j

  -- | Build the self-coupling matrix of a linear map @j -> j@ by probing
  -- each basis vector of the /given/ dimension.  The dimension is explicit:
  -- it cannot be recovered from the map itself (probing requires a
  -- well-formed input, and strict channels reject under-length ones).
  selfMatrix :: Int -> (j -> j) -> Matrix (Scalar j)

  -- | Apply a matrix to a channel cotangent.
  applyMatrix :: Matrix (Scalar j) -> j -> j

-- | One-dimensional channel over a 'NHR.StarSemiring' scalar.
instance StarChannel FieldStar where
  type Scalar FieldStar = FieldStar
  channelDim _ = 1
  zeroChannel _ = NHA.zero
  basisChannel _ _ = NHM.one
  addChannel (FieldStar x) (FieldStar y) = FieldStar (x P.+ y)
  negateChannel (FieldStar x) = FieldStar (P.negate x)
  selfMatrix _ f = fromLists [[f NHM.one]]
  applyMatrix m v = case toLists m of
    [[s]] -> s NHM.* v
    _ -> error "Circuit.Diff.Eliminate.applyMatrix: scalar channel expected a 1x1 matrix"

-- | n-dimensional channel as a list of scalar cotangents.
--
-- Requires 'NHA.Subtractive' on the element for 'negateChannel' — note that
-- @numhask-free@'s 'FieldStar' already carries this instance, so @[FieldStar]@
-- channels are usable here.
instance
  ( NHR.StarSemiring a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a
  ) =>
  StarChannel [a]
  where
  type Scalar [a] = a
  channelDim = length
  zeroChannel n = replicate n NHA.zero
  basisChannel n i = [if k == i then NHM.one else NHA.zero | k <- [0 .. n - 1]]
  addChannel = zipWith (NHA.+)
  negateChannel = fmap NHA.negate
  selfMatrix n f =
    let cols = [f (basisChannel n i) | i <- [0 .. n - 1]]
     in fromLists [[col !! k | col <- cols] | k <- [0 .. n - 1]]
  applyMatrix = matVec

-- | 'FieldStar' as a numeric carrier for circuits' additive structure, so
-- hand-built nets can use structural rows at 'FieldStar' types.  (Nets from
-- 'Circuit.Diff.Backprop.linearizeAt' never need this — their structural rows are
-- already 'Lift's.)  Deliberately orphan: this module is the federation
-- seam between @circuits@ and @numhask-free@.
instance Circuit.Dagger.Merge (->) FieldStar where
  plus (FieldStar x, FieldStar y) = FieldStar (x P.+ y)

instance Circuit.Dagger.Zero (->) FieldStar where
  zero _ = FieldStar 0

-- | Solve one affine knot body in closed form.
--
-- For a body @f :: (j, c) -> (j, b)@ (channel cotangent, output cotangent),
-- affinity gives @f₁ (dj, dc) = A·dj + C·dc@.  The probes:
--
-- > C·dc = f₁ (0, dc)                       -- one call, at the true zero
-- > A·e_i = f₁ (e_i, dc) − C·dc             -- offset-subtracted: valid at dc ≠ 0
-- > dj   = star A · C·dc                    -- starMatrix
-- > db   = f₂ (dj, dc)                      -- one final call
--
-- The offset subtraction is what lets every probe run at the /actual/
-- cotangent @dc@, so no @zero@ for the (existential) type @c@ is ever
-- needed.  Cost: @dim + 2@ body calls per cotangent; the star is /not/
-- shared across cotangents — that is the price of the existential.
solveAffine ::
  (StarChannel j) =>
  Int ->
  ((j, c) -> (j, b)) ->
  c ->
  b
solveAffine dim body dc =
  let zeroJ = zeroChannel dim
      cdc = fst (body (zeroJ, dc))
      negCdc = negateChannel cdc
      aMat = selfMatrix dim (\dk -> addChannel (fst (body (dk, dc))) negCdc)
      dj = applyMatrix (starMatrix aMat) cdc
   in snd (body (dj, dc))

-- | Eliminate all @(,)@ knots in a linear pullback net, structurally.
--
-- Structural rows are melted first ('melt'); then the
-- recursion replaces each 'Trace' — innermost first, so a knot body handed
-- to 'solveAffine' is already loop-free and can be evaluated by plain
-- 'run' — with one solved 'Lift'.  Everything else keeps its shape.
--
-- __The channel witness__: pass a sample channel cotangent (its value is
-- irrelevant; its /dimension/ is read with 'channelDim').  The channel type
-- inside 'Trace' is existential, so the witness is matched by 'unsafeCoerce'.
--
-- __Precondition (caller-checked, not machine-checked)__: every knot in the
-- net has channel type @j@ with the witness's dimension.  This holds for
-- single-loop nets from 'Circuit.Diff.Backprop.linearizeAt' over a @j@ channel; it is
-- /not/ guaranteed for arbitrary nets — distinct knots may close over
-- distinct channel types, and a mismatched coercion is undefined behaviour.
-- The principled fix is evidence on the row: a 'StarChannel' dictionary
-- captured by the 'Trace' constructor at linearization time, which would
-- delete both the witness argument and the coercion.  That is a @circuits@
-- GADT decision, not patchable from this module.
--
-- A self-coupled scalar loop the lazy trace diverges on, solved exactly
-- (@dj = 0.3·dj + 2·dc@, @db = dj@, so @db\/dc = 2\/0.7@):
--
-- >>> :{
-- let body (FieldStar dj, dc) = (FieldStar (0.3 * dj + 2.0 * dc), dj)
--     net = Knot (Lift (Pullback body)) :: Net (,) (,) Pullback Double Double
-- :}
--
-- >>> let solved = eliminateKnots (FieldStar 0) net
-- >>> abs (evalPullback solved 1.0 - 2.0 / 0.7) < 1e-12
-- True
eliminateKnots ::
  forall j b a.
  (StarChannel j) =>
  j ->
  Net (,) (,) Pullback b a ->
  Net (,) (,) Pullback b a
eliminateKnots witness net = go (melt net)
  where
    dim = channelDim witness

    go :: forall x y. Net (,) (,) Pullback x y -> Net (,) (,) Pullback x y
    go n = case n of
      Lift p -> Lift p
      Compose g f -> Compose (go g) (go f)
      Par f g -> Par (go f) (go g)
      Swap -> Swap
      Knot f ->
        let f' = go f -- innermost first: body is knot-free below here
            body =
              runPullback
                (run (unsafeCoerce f' :: Net (,) (,) Pullback (j, x) (j, y)))
         in Lift (Pullback (solveAffine dim body))
      Copy -> unreachableRow "Copy"
      Discard -> unreachableRow "Discard"
      Plus -> unreachableRow "Plus"
      Zero -> unreachableRow "Zero"

    unreachableRow name =
      error $
        "Circuit.Diff.Eliminate.eliminateKnots: structural "
          ++ name
          ++ " row after melt (impossible)"
