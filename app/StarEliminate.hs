-- | Tests for star-elimination of '(,)' knots in linear pullback nets.
module StarEliminate
  ( runStarEliminateTests,
  )
where

import Circuit.Diff.Backprop (linearizeAt)
import Circuit.Diff.Circuit (Diff (..))
import Circuit.Diff.Eliminate (eliminateKnots, fieldStarEvidence, listEvidence)
import Circuit.Diff.Pullback (Pullback (..), evalPullback)
import Circuit.Net (Net (..))
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Free.Carriers (FieldStar (..))
import Prelude hiding (id, (.))

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else error $ "FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected

-- | Scalar pullback knot:
--
-- > (dx, db) = body (dx, dc)  where  dx' = 0.5*dx + dc,  db = dx + 2*dc
--
-- The trace equation is @dx = 0.5*dx + dc@, solved by @dx = 2*dc@.
-- Then @db = dx + 2*dc = 4*dc@.
scalarKnot :: Net (,) (,) Pullback FieldStar FieldStar
scalarKnot =
  Knot
    fieldStarEvidence
    ( Lift
        ( Pullback $ \(FieldStar dx, FieldStar dc) ->
            (FieldStar (0.5 * dx + dc), FieldStar (dx + 2.0 * dc))
        )
    )

runStarEliminateTests :: IO ()
runStarEliminateTests = do
  putStrLn "Star-eliminate scalar pullback knot"
  let eliminated = eliminateKnots scalarKnot
      FieldStar g1 = evalPullback eliminated (FieldStar 1.0)
      FieldStar g3 = evalPullback eliminated (FieldStar 3.0)
  assert "eliminated scalar gradient" g1 4.0
  assert "eliminated scalar gradient at 3" g3 12.0

  putStrLn "Star-eliminate vector pullback knot"
  -- Two-dimensional channel over [FieldStar]:
  --   dx1' = 0.5*dx1 + 0.1*dx2 + dc
  --   dx2' = 0.2*dx1 + 0.3*dx2 + 2*dc
  --   db   = dx1 + dx2 + dc
  -- Solve (I - A) dx = C dc where A = [[0.5,0.1],[0.2,0.3]], C = [1,2].
  -- For dc = 1, analytic solution:
  --   det = (1-0.5)*(1-0.3) - (-0.1)*(-0.2) = 0.5*0.7 - 0.02 = 0.33
  --   dx1 = (0.7*1 + 0.1*2) / 0.33 = 0.9/0.33 = 30/11
  --   dx2 = (0.2*1 + 0.5*2) / 0.33 = 1.2/0.33 = 40/11
  --   db  = dx1 + dx2 + 1 = 70/11 + 1 = 81/11
  let vecBody =
        Pullback $ \(dxs, FieldStar dc) ->
          let dxs' = map unFieldStar (take 2 (dxs ++ repeat NHA.zero))
              (dx1, dx2) = case dxs' of (x : y : _) -> (x, y); _ -> (NHA.zero, NHA.zero)
           in ( [ FieldStar (0.5 * dx1 + 0.1 * dx2 + dc),
                  FieldStar (0.2 * dx1 + 0.3 * dx2 + 2.0 * dc)
                ],
                FieldStar (dx1 + dx2 + dc)
              ) ::
                ([FieldStar], FieldStar)
      vecKnot = Knot (listEvidence 2) (Lift vecBody) :: Net (,) (,) Pullback FieldStar FieldStar
      eliminatedVec = eliminateKnots vecKnot
      FieldStar gVec = evalPullback eliminatedVec (FieldStar 1.0)
      expectedVec = (30.0 / 11.0) + (40.0 / 11.0) + 1.0
  assert "eliminated vector gradient" gVec expectedVec

  putStrLn "Melt structural rows around a knot"
  let copiedKnot =
        Compose Plus (Compose (Par scalarKnot scalarKnot) Copy) ::
          Net (,) (,) Pullback FieldStar FieldStar
      eliminatedCopy = eliminateKnots copiedKnot
      FieldStar gCopy = evalPullback eliminatedCopy (FieldStar 1.0)
  assert "melted copy-add around knot" gCopy 8.0

  putStrLn "Star-eliminate via composition"
  let scale3 = Lift (Pullback (\(FieldStar x) -> FieldStar (3.0 * x)))
      nested = Compose scale3 scalarKnot :: Net (,) (,) Pullback FieldStar FieldStar
      eliminatedNested = eliminateKnots nested
      FieldStar gNested = evalPullback eliminatedNested (FieldStar 1.0)
  assert "composition" gNested 12.0

  putStrLn "Integration: linearize lazy Diff knot, then eliminate"
  -- Forward body has zero channel self-coupling so the lazy Diff knot
  -- converges.  The pullback body has channel coupling 0.5, which would
  -- diverge under the lazy Pullback trace; after elimination it is exact.
  let innerBody =
        Diff
          ( \(FieldStar x, FieldStar b) ->
              ( (NHA.zero, FieldStar 0.5 NHM.* FieldStar x NHA.+ FieldStar b),
                \(FieldStar _dy1, FieldStar dy2) ->
                  (FieldStar 0.5 NHM.* FieldStar dy2, FieldStar dy2)
              )
          ) ::
          Diff () (FieldStar, FieldStar) (FieldStar, FieldStar)
      innerKnot = Knot fieldStarEvidence (Lift innerBody) :: Net (,) (,) (Diff ()) FieldStar FieldStar
      (FieldStar y, g) = linearizeAt innerKnot (FieldStar 4.0)
      gElim = eliminateKnots g
      FieldStar gLazy = evalPullback g (FieldStar 1.0)
      FieldStar gElimVal = evalPullback gElim (FieldStar 1.0)
  assert "lazy-knot value" y 4.0
  assert "lazy-knot gradient" gLazy 1.0
  assert "eliminated lazy-knot gradient" gElimVal 1.0
