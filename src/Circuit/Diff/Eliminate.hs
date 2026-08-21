{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Star-elimination of @(,)@ knots in linear 'Pullback' loops.
--
-- A 'C.Loop (,) Pullback' built by 'Circuit.Diff.Backprop.linearizeLoop' is
-- linear by construction: every 'C.Lift' is a pointwise pullback and every
-- 'C.Knot' ties an affine feedback equation.  This module eliminates those
-- knots in closed form using the Kleene star
-- ('NumHask.Algebra.Ring.StarSemiring' for scalar channels,
-- 'Circuit.Mat.Dense.starMatrix' for vector channels).
--
-- The pass is /structural/: it recurses through the loop, replaces each
-- 'C.Knot' — innermost first, Bekić order — with a single solved 'C.Lift', and
-- leaves every other constructor in place.  The result preserves the loop's
-- shape minus its loops, so it can be evaluated on strict carriers without
-- the lazy-knot divergence that 'Traced' @Pullback (,)@ suffers when channel
-- self-coupling is non-zero — and it remains inspectable: the only opaque
-- nodes are the ones Gaussian elimination genuinely created.
--
-- The channel structure is read from the 'StarChannel' value carried on the
-- feedback wire.  Knots whose feedback channel is not 'StarChannel' are not
-- touched by this pass.
module Circuit.Diff.Eliminate
  ( -- * Trace elimination
    eliminateKnots,
  )
where

import Circuit.Dagger qualified
import Circuit.Diff.Evidence (StarChannel (..))
import Circuit.Diff.Pullback (Pullback (..))
import Circuit.Layer (run)
import Circuit.Loop qualified as C
import NumHask.Free.Carriers (FieldStar (..))
import Unsafe.Coerce (unsafeCoerce)
import Prelude hiding (id, (.))
import Prelude qualified as P

-- $setup
-- >>> import Circuit.Diff.Evidence (fieldStarChannel, listStarChannel, withStarChannel)
-- >>> import Circuit.Diff.Pullback (Pullback (..))
-- >>> import Circuit.Loop (Loop (..))
-- >>> import NumHask.Free.Carriers (FieldStar (..))
-- >>> import Prelude hiding (id, (.))

-- | 'FieldStar' as a numeric carrier for circuits' additive structure, so
-- hand-built loops can use structural rows at 'FieldStar' types.  (Loops from
-- 'Circuit.Diff.Backprop.linearizeLoop' never need this — their structural rows
-- are already 'C.Lift's.)
--
-- These instances remain necessary because structural rows ('Plus', 'Zero')
-- carry 'MergeT' / 'ZeroT' constraints that resolve to 'Merge' / 'Zero' on
-- the wiring arrow.  For 'Pullback FieldStar' those constraints bottom out in
-- 'Merge (->) FieldStar' and 'Zero (->) FieldStar'.  Deliberately orphan: this
-- module is the federation seam between @circuits@ and @numhask-free@.
instance Circuit.Dagger.Merge (->) FieldStar where
  plus (FieldStar x, FieldStar y) = FieldStar (x P.+ y)

instance Circuit.Dagger.Zero (->) FieldStar where
  zero _ = FieldStar 0

-- | Solve one affine knot body in closed form.
--
-- For a body @f :: (StarChannel j, c) -> (StarChannel j, b)@ (channel
-- cotangent, output cotangent), affinity gives @f₁ (dj, dc) = A·dj + C·dc@.
-- The probes:
--
-- > C·dc = f₁ (0, dc)                       -- one call, at the true zero
-- > A·e_i = f₁ (e_i, dc) − C·dc             -- offset-subtracted: valid at dc ≠ 0
-- > dj   = star A · C·dc                    -- starMatrix
-- > db   = f₂ (dj, dc)                      -- one final call
--
-- The dictionary is recovered from the output of a lazy probe: a knot body
-- built with 'Circuit.Diff.Evidence.withStarChannel' carries the same
-- dictionary through the trace, so pattern-matching the output reveals it
-- without evaluating the input data.
--
-- The offset subtraction is what lets every probe run at the /actual/
-- cotangent @dc@, so no @zero@ for the (existential) type @c@ is ever
-- needed.  Cost: @dim + 2@ body calls per cotangent; the star is /not/
-- shared across cotangents — that is the price of the existential.
solveAffine ::
  forall j c b.
  ((StarChannel j, c) -> (StarChannel j, b)) ->
  c ->
  b
solveAffine body dc =
  let -- A bottom value of type 'StarChannel j'.  Only the constructor is
      -- needed; the fields are supplied lazily by the body's output.
      probe :: StarChannel j
      probe =
        StarChannel
          { starDim = error "Circuit.Diff.Eliminate.solveAffine: probe dim evaluated",
            starData = error "Circuit.Diff.Eliminate.solveAffine: probe data evaluated",
            starZero = error "Circuit.Diff.Eliminate.solveAffine: probe zero evaluated",
            starBasis = error "Circuit.Diff.Eliminate.solveAffine: probe basis evaluated",
            starAdd = error "Circuit.Diff.Eliminate.solveAffine: probe add evaluated",
            starNegate = error "Circuit.Diff.Eliminate.solveAffine: probe negate evaluated",
            starSelfMatrix = error "Circuit.Diff.Eliminate.solveAffine: probe selfMatrix evaluated",
            starApplyMatrix = error "Circuit.Diff.Eliminate.solveAffine: probe applyMatrix evaluated",
            starMatrix = error "Circuit.Diff.Eliminate.solveAffine: probe matrix evaluated"
          }
      (scOut, _) = body (probe, dc)
      zeroJ = starZero scOut (starDim scOut)
      zeroSC = scOut {starData = zeroJ}
      cdc = starData (fst (body (zeroSC, dc)))
      negCdc = starNegate scOut cdc
      aMat =
        starSelfMatrix
          scOut
          (starDim scOut)
          (\dk -> starAdd scOut (starData (fst (body (zeroSC {starData = dk}, dc)))) negCdc)
      dj = starApplyMatrix scOut (starMatrix scOut aMat) cdc
   in snd (body (zeroSC {starData = dj}, dc))

-- | Eliminate all @(,)@ knots whose feedback channel is 'StarChannel' in a
-- linear pullback loop, structurally.
--
-- The recursion replaces each 'C.Knot' — innermost first, so a knot body
-- handed to 'solveAffine' is already loop-free and can be evaluated by plain
-- 'run' — with one solved 'C.Lift'.  Everything else keeps its shape.
--
-- A self-coupled scalar loop the lazy trace diverges on, solved exactly
-- (@dj = 0.3·dj + 2·dc@, @db = dj@, so @db\/dc = 2\/0.7@):
--
-- >>> :{
-- let body (FieldStar dj, dc) = (FieldStar (0.3 * dj + 2.0 * dc), dj)
--     loop = Knot (withStarChannel fieldStarChannel (Lift (Pullback body))) :: Loop (,) Pullback Double Double
-- :}
--
-- >>> let solved = eliminateKnots loop
-- >>> abs (run solved 1.0 - 2.0 / 0.7) < 1e-12
-- True
eliminateKnots ::
  forall a b.
  C.Loop (,) Pullback b a ->
  C.Loop (,) Pullback b a
eliminateKnots n = case n of
  C.Lift p -> C.Lift p
  C.Knot f ->
    let body = runPullback f
        body' :: forall j. (StarChannel j, b) -> (StarChannel j, a)
        body' = unsafeCoerce body
     in C.Lift (Pullback (solveAffine body'))
