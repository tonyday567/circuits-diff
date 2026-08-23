{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeFamilies #-}

-- | Star-elimination evidence as a channel type.
--
-- The insight is that star-elimination structure is /data carried on a wire/,
-- not wiring itself.  @circuits@ keeps 'Circuit.Trace.yank' free of evidence;
-- 'circuits-diff' instead uses a channel whose values carry their own
-- elimination dictionary.
--
-- A @StarChannel s@ is both the feedback state (the @s@ field) and the
-- dictionary needed to solve affine feedback equations over that state.  The
-- dictionary part of the value is carried through the trace unchanged; the
-- data part is updated by the knot body.
module Circuit.Diff.Evidence
  ( -- * Evidence-carrying channel
    StarChannel (..),
    Scalar,

    -- * Concrete channels
    fieldStarChannel,
    listStarChannel,

    -- * Wrappers for knot bodies
    withStarChannel,
    withStarChannelDiff,
  )
where

import Circuit.Diff (Diff (..))
import Circuit.Mat.Dense (Matrix (..), fromLists, matVec, toLists)
import Circuit.Mat.Dense qualified as MD
import Circuit.Pullback (Pullback (..))
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import NumHask.Free.Carriers (FieldStar (..))
import NumHask.Prelude hiding (Scalar)

-- | Scalar carrier associated with a star-channel state type.
--
-- For scalar channels the scalar is the state itself; for list channels it
-- is the list element type.
type family Scalar s

type instance Scalar FieldStar = FieldStar

type instance Scalar [a] = a

-- | A feedback channel that carries its own star-elimination dictionary.
--
-- The matrix carrier is fixed by the 'Scalar' type family so that
-- @circuits-diff@ (which already depends on @circuits-mat@) can use dense
-- matrices directly, while @circuits@ remains ignorant of matrices.
--
-- A value bundles the current feedback state ('starData') with the operations
-- needed to eliminate a self-coupled affine knot over that state.  The
-- dictionary fields are expected to be preserved by a knot body;
-- 'withStarChannel' and 'withStarChannelDiff' are the canonical ways to build
-- such bodies.
data StarChannel s = StarChannel
  { -- | Dimension of the channel cotangent space.
    starDim :: Int,
    -- | Current feedback state.
    starData :: s,
    -- | Zero channel cotangent of the given dimension.
    starZero :: Int -> s,
    -- | Basis vector @e_i@: @starBasis dim i@.
    starBasis :: Int -> Int -> s,
    -- | Componentwise sum of two channel cotangents.
    starAdd :: s -> s -> s,
    -- | Additive inverse of a channel cotangent.
    starNegate :: s -> s,
    -- | Build the self-coupling matrix of a linear map @s -> s@ by
    -- probing each basis vector of the given dimension.
    starSelfMatrix :: Int -> (s -> s) -> Matrix (Scalar s),
    -- | Apply a matrix to a channel cotangent.
    starApplyMatrix :: Matrix (Scalar s) -> s -> s,
    -- | Kleene star of a square self-coupling matrix.
    starMatrix :: Matrix (Scalar s) -> Matrix (Scalar s)
  }

-- | Evidence for a one-dimensional 'FieldStar' channel.
--
-- The matrix carrier is @'Matrix' 'FieldStar'@ — a 1×1 matrix whose single
-- element is the scalar channel cotangent.
fieldStarChannel :: StarChannel FieldStar
fieldStarChannel =
  StarChannel
    { starDim = 1,
      starData = NHA.zero,
      starZero = const NHA.zero,
      starBasis = \_ _ -> NHM.one,
      starAdd = (NHA.+),
      starNegate = NHA.negate,
      starSelfMatrix = \_ f -> fromLists [[f NHM.one]],
      starApplyMatrix = \m v -> case toLists m of
        [[s]] -> s NHM.* v
        _ -> error "Circuit.Diff.Evidence.applyMatrixE: scalar channel expected a 1x1 matrix",
      starMatrix = MD.starMatrix
    }

-- | Evidence for an n-dimensional list channel.
--
-- The matrix carrier is @'Matrix' a@; the channel cotangent is @[a]@.
listStarChannel ::
  ( NHR.StarSemiring a,
    NHA.Subtractive a
  ) =>
  Int ->
  StarChannel [a]
listStarChannel dim =
  let basis n i = [if k == i then NHM.one else NHA.zero | k <- [0 .. n - 1]]
      zero n = replicate n NHA.zero
   in StarChannel
        { starDim = dim,
          starData = zero dim,
          starZero = zero,
          starBasis = basis,
          starAdd = zipWith (NHA.+),
          starNegate = fmap NHA.negate,
          starSelfMatrix = \n f ->
            let cols = [f (basis n i) | i <- [0 .. n - 1]]
             in fromLists [[col !! k | col <- cols] | k <- [0 .. n - 1]],
          starApplyMatrix = matVec,
          starMatrix = MD.starMatrix
        }

-- | Wrap a pullback computation on the underlying channel @s@ into a
-- computation on 'StarChannel' @s@.
--
-- The supplied @dict@ provides the elimination dictionary; the body only
-- needs to update 'starData'.  The output value reuses @dict@'s dictionary
-- fields, so 'Circuit.Diff.Star.solveStarBody' can read them directly from
-- the exposed channel type.
withStarChannel ::
  StarChannel s ->
  Pullback (s, b) (s, c) ->
  Pullback (StarChannel s, b) (StarChannel s, c)
withStarChannel dict (Pullback body) =
  Pullback
    ( \(sc, b) ->
        let (s', c) = body (starData sc, b)
         in (dict {starData = s'}, c)
    )

-- | Wrap a 'Diff' computation on the underlying channel @s@ into a
-- computation on 'StarChannel' @s@.
--
-- This is the forward-differentiable analogue of 'withStarChannel': the
-- forward pass threads the 'StarChannel' state, and the backward pass
-- threads its cotangent through the same dictionary.
withStarChannelDiff ::
  StarChannel s ->
  Diff p (s, b) (s, c) ->
  Diff p (StarChannel s, b) (StarChannel s, c)
withStarChannelDiff dict (Diff body) =
  Diff
    ( \(sc, b) ->
        let ((s', c), back) = body (starData sc, b)
            sc' = dict {starData = s'}
            backward (dsc, dc) =
              let (ds, db) = back (starData dsc, dc)
               in (dict {starData = ds}, db)
         in ((sc', c), backward)
    )
