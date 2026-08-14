{-# LANGUAGE PatternSynonyms #-}

-- | The Schur-complement bridge — 'trace' solved by 'starMatrix'.
--
-- This is where the three floors actually touch.  A 'Diff' knot body
-- has a backward pass that is /affine in cotangents/ (calculus
-- promises linearity), so its channel self-coupling is a linear map
-- recoverable by probing with basis cotangents.  Build that map as a
-- 'Matrix', take its Kleene star with 'starMatrix' — Gaussian
-- elimination, @(I − A)⁻¹@, the fourth face of the four-for-one — and
-- the trace's pullback is the Schur complement
--
-- > db = D·dc + B · star A · C·dc
--
-- recovered with one final probe at the backward fixpoint.
--
-- Cost: @dim@ probes of @backward@ plus one @starMatrix@ per forward
-- point, /shared across all cotangents/; each subsequent pullback is
-- two probes and a matrix–vector product.  Compare 'Circuit.Diff.Circuit.traceNFrom',
-- which pays @n@ probes per cotangent and is only as exact as @n@ is
-- large.  Here the backward pass is exact whenever the star exists.
--
-- The dependency is deliberate: this module imports "Circuit.Mat.Dense",
-- making circuits-ad ⇄ star-matrix a literal edge rather than a nominal
-- alias.
module Circuit.Diff.Star
  ( -- * Polymorphic bridge
    traceStarMatrix,

    -- * Double adapters (via 'FieldStar')
    traceStarFromD,
    traceStarMatrixD,
  )
where

import Circuit.Diff.Circuit (Diff, Diff', traceStarFrom, pattern Diff)
import Circuit.Mat.Dense (Matrix (..), fromLists, matVec, starMatrix)
import Circuit.Dagger (MergeZero (..))
import Circuit.Dagger qualified as CD
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import NumHask.Free.Carriers (FieldStar (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Diff.Circuit (Diff (..))
-- >>> import Prelude hiding (id, (.))

-- | Trace over a /vector/ feedback channel, backward pass solved by
-- 'starMatrix'.
--
-- The channel is a list @[j]@ whose dimension is fixed by the seed.
-- Forward iterates from the seed (no closed form for a nonlinear
-- fixpoint).  Backward:
--
--   1. probe @backward@ with each basis cotangent @e_i@ to read off
--      column @i@ of the channel self-coupling A (in cotangent space);
--   2. @star A@ by Conway block recursion — 'starMatrix';
--   3. per cotangent @dc@: @C·dc = fst (backward (0, dc))@, then
--      @db = snd (backward (star A · C·dc, dc))@.
--
-- A and @star A@ are forced once (lazily, on first pullback) and
-- shared across cotangents.
--
-- __Proof obligation__: probing assumes every primitive's pullback is
-- a genuinely linear map — true for honestly-constructed 'Diff' prims.
traceStarMatrix ::
  (NHR.StarSemiring j, MergeZero (->) c) =>
  -- | forward seed; its length is the channel dimension
  [j] ->
  -- | forward iteration count
  Int ->
  Diff' p ([j], b) ([j], c) ->
  Diff' p b c
traceStarMatrix x0 n (Diff body) = Diff $ \b ->
  let dim = length x0
      -- Forward: iterate from caller-supplied seed
      stepFwd x = let ((x', _), _) = body (x, b) in x'
      a = iterate stepFwd x0 !! n
      ((_, c), backward) = body (a, b)
      -- Channel self-coupling, column i = backward probe at e_i
      zeroV = replicate dim NHA.zero
      basis i = [if k == i then NHM.one else NHA.zero | k <- [0 .. dim - 1]]
      cols = [fst (backward (basis i, CD.zero ())) | i <- [0 .. dim - 1]]
      aMat = fromLists [[col !! k | col <- cols] | k <- [0 .. dim - 1]]
      -- star A — Gaussian elimination / Warshall / Floyd–Warshall /
      -- state elimination, depending on the carrier
      aStar = starMatrix aMat
      pullback dc =
        let cdc = fst (backward (zeroV, dc))
         in snd (backward (matVec aStar cdc, dc))
   in (c, pullback)

-- | 'Circuit.Diff.Circuit.traceStarFrom' for a bare 'Double' channel, routed
-- through 'FieldStar' so @star a = recip (1 − a)@ is the class
-- method, not an ad-hoc formula.
--
-- Channel @x' = 0.3x + b@, output @c = 2x@.  The fixpoint is
-- @x = b\/0.7@, so @dc\/db = 2\/0.7 ≈ 2.857@ — the same number the
-- Neumann iteration approaches, computed here in closed form:
--
-- >>> :{
-- let body = Diff (\(x, b) ->
--       ( (0.3 * x + b, 2.0 * x)
--       , \(dx', dc) -> (0.3 * dx' + 2.0 * dc, dx') ))
-- :}
--
-- >>> let (y, pb) = runDiff (traceStarFromD 0 60 body) 1.0
-- >>> abs (y - 2.0 / 0.7) < 1e-12
-- True
-- >>> abs (pb 1.0 - 2.0 / 0.7) < 1e-12
-- True
traceStarFromD ::
  (MergeZero (->) c) =>
  Double ->
  Int ->
  Diff' p (Double, b) (Double, c) ->
  Diff' p b c
traceStarFromD x0 n (Diff body) =
  traceStarFrom (FieldStar x0) n (Diff body')
  where
    body' (FieldStar x, b) =
      let ((x', c), back) = body (x, b)
       in ( (FieldStar x', c),
            \(FieldStar dx', dc) ->
              let (dx, db) = back (dx', dc)
               in (FieldStar dx, db)
          )

-- | 'traceStarMatrix' for bare @[Double]@ channels, routed through
-- 'FieldStar' so 'starMatrix' performs honest @(I − A)⁻¹@.
--
-- A two-dimensional channel: @x' = 0.5y + b@, @y' = 0.3x@, output
-- @c = x + 2y@.  Solving the fixpoint by hand: @x = b\/0.85@,
-- @y = 0.3b\/0.85@, @c = 1.6b\/0.85@, so @dc\/db = 1.6\/0.85@.
--
-- >>> :{
-- let body2 = Diff (\([x, y], b) ->
--       ( ([0.5 * y + b, 0.3 * x], x + 2.0 * y)
--       , \([dx', dy'], dc) -> ([0.3 * dy' + dc, 0.5 * dx' + 2.0 * dc], dx') ))
-- :}
--
-- >>> let (y2, pb2) = runDiff (traceStarMatrixD [0, 0] 200 body2) 1.0
-- >>> abs (y2 - 1.6 / 0.85) < 1e-12
-- True
-- >>> abs (pb2 1.0 - 1.6 / 0.85) < 1e-12
-- True
traceStarMatrixD ::
  (MergeZero (->) c) =>
  [Double] ->
  Int ->
  Diff' p ([Double], b) ([Double], c) ->
  Diff' p b c
traceStarMatrixD x0 n (Diff body) =
  traceStarMatrix (map FieldStar x0) n (Diff body')
  where
    wrap = map FieldStar
    unwrap = map (\(FieldStar d) -> d)
    body' (js, b) =
      let ((xs, c), back) = body (unwrap js, b)
       in ( (wrap xs, c),
            \(djs, dc) ->
              let (dxs, db) = back (unwrap djs, dc)
               in (wrap dxs, db)
          )
