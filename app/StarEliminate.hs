-- | Tests for star-elimination of '(,)' knots in linear pullback bodies.
module StarEliminate
  ( runStarEliminateTests,
  )
where

import Circuit.Body (Body (..))
import Circuit.Category ((.))
import Circuit.Diff.Backprop (linearizeBody)
import Circuit.Diff.Circuit (Diff (..))
import Circuit.Diff.Evidence
  ( StarChannel (..),
    fieldStarChannel,
    listStarChannel,
    withStarChannel,
    withStarChannelDiff,
  )
import Circuit.Diff.Star (solveStarBody)
import Circuit.Pullback (Pullback (..))
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

-- | Scalar pullback body:
--
-- > (dx, db) = body (dx, dc)  where  dx' = 0.5*dx + dc,  db = dx + 2*dc
--
-- The trace equation is @dx = 0.5*dx + dc@, solved by @dx = 2*dc@.
-- Then @db = dx + 2*dc = 4*dc@.
scalarKnot :: Body (,) (StarChannel FieldStar) Pullback FieldStar FieldStar
scalarKnot =
  Body $
    withStarChannel fieldStarChannel $
      Pullback
        ( \(FieldStar dx, FieldStar dc) ->
            ( FieldStar (0.5 * dx + dc),
              FieldStar (dx + 2.0 * dc)
            )
        )

runStarEliminateTests :: IO ()
runStarEliminateTests = do
  putStrLn "Star-eliminate scalar pullback body"
  let eliminated = solveStarBody scalarKnot
      FieldStar g1 = runPullback eliminated (FieldStar 1.0)
      FieldStar g3 = runPullback eliminated (FieldStar 3.0)
  assert "eliminated scalar gradient" g1 4.0
  assert "eliminated scalar gradient at 3" g3 12.0

  putStrLn "Star-eliminate vector pullback body"
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
        Pullback
          ( \(dxs, FieldStar dc) ->
              let dxs' = map unFieldStar (take 2 (dxs ++ repeat NHA.zero))
                  (dx1, dx2) = case dxs' of (x : y : _) -> (x, y); _ -> (NHA.zero, NHA.zero)
               in ( [ FieldStar (0.5 * dx1 + 0.1 * dx2 + dc),
                      FieldStar (0.2 * dx1 + 0.3 * dx2 + 2.0 * dc)
                    ],
                    FieldStar (dx1 + dx2 + dc)
                  ) ::
                    ([FieldStar], FieldStar)
          )
      vecKnot = Body (withStarChannel (listStarChannel 2) vecBody)
      eliminatedVec = solveStarBody vecKnot
      FieldStar gVec = runPullback eliminatedVec (FieldStar 1.0)
      expectedVec = (30.0 / 11.0) + (40.0 / 11.0) + 1.0
  assert "eliminated vector gradient" gVec expectedVec

  putStrLn "Star-eliminate via composition"
  let scale3 = Body (Pullback (\(sc, FieldStar x) -> (sc, FieldStar (3.0 * x))))
      nested = scale3 . scalarKnot
      eliminatedNested = solveStarBody nested
      FieldStar gNested = runPullback eliminatedNested (FieldStar 1.0)
  assert "composition" gNested 12.0

  putStrLn "Integration: linearize lazy Diff body, then eliminate"
  -- Forward body has zero channel self-coupling so the lazy Diff knot
  -- converges.  The pullback body has channel coupling 0.5, which would
  -- diverge under a strict Pullback trace; after elimination it is exact.
  let innerBodyRaw =
        Diff
          ( \(FieldStar x, FieldStar b) ->
              ( (NHA.zero, FieldStar 0.5 NHM.* FieldStar x NHA.+ FieldStar b),
                \(FieldStar _dy1, FieldStar dy2) ->
                  (FieldStar 0.5 NHM.* FieldStar dy2, FieldStar dy2)
              )
          ) ::
          Diff () (FieldStar, FieldStar) (FieldStar, FieldStar)
      innerBody = Body (withStarChannelDiff fieldStarChannel innerBodyRaw)
      (FieldStar y, g) = linearizeBody innerBody (FieldStar 4.0)
      gElim = solveStarBody g
      (_, FieldStar gLazy) = runPullback (morphism g) (fieldStarChannel, FieldStar 1.0)
      FieldStar gElimVal = runPullback gElim (FieldStar 1.0)
  assert "lazy-knot value" y 4.0
  assert "lazy-knot gradient" gLazy 1.0
  assert "eliminated lazy-knot gradient" gElimVal 1.0
