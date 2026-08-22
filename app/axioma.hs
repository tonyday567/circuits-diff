{-# LANGUAGE RebindableSyntax #-}

module Main (main) where

import Circuit (Trace, base)
import Circuit.Syntax (eval)
import Circuit qualified
import Circuit.Body (Body (..))
import Circuit.Channel (Traced (..))
import Circuit.Diff.Backprop (linearizeAt, linearizeBody)
import Circuit.Diff.Circuit (Diff (..), Diff', runDiff, traceNFrom)
import Circuit.Diff.Pullback (Pullback (..), evalPullback)
import Circuit.Net (Net (..), lift)
import DiffCarrierTests (runDiffCarrierTests)
import Kepler (runKeplerTests)
import MatrixStar (runMatrixStarTests)
import MetricAdjoint (runMetricAdjointTests)
import NumHask.Prelude
import Operators (runOperatorTests)
import StarEliminate (runStarEliminateTests)
import StreamTower (runStreamTowerTests)
import System.Exit (exitFailure)
import Tags (runTagTests)
import Tensor (runTensorTests)

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else do
      putStrLn $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected
      exitFailure

sq :: Diff' Double Double
sq = Diff (\x -> (x * x, \d -> 2 * x * d))

constD :: Double -> Diff' Double Double
constD c = Diff (const (c, const 0))

-- | Net computing 2*x^2 via copy, parallel squares, then add.
quadNet :: Net (,) Diff' Double Double
quadNet = Compose Plus (Compose (Par (lift sq) (lift sq)) Copy)

-- | Linear feedback loop: x' = 0.3*x + 2*b, c = x + b.
loopBody :: Diff' (Double, Double) (Double, Double)
loopBody = Diff $ \(x, b) ->
  let x' = 0.3 * x + 2 * b
      c = x + b
   in ((x', c), \(dx', dc) -> (0.3 * dx' + 2 * dc, dx' + dc))

main :: IO ()
main = do
  putStrLn "nonlinear 2x^2 net"
  let (y, g) = linearizeAt quadNet 3.0
  assert "value" y 18.0
  assert "gradient" (evalPullback g 1.0) 12.0

  putStrLn "strict feedback via traceNFrom"
  let (yLoop, pbLoop) = runDiff (traceNFrom 0.0 200 loopBody) 1.0
  assert "value" yLoop (1.0 / (1.0 - 0.3) * 2.0 + 1.0)
  assert "gradient" (pbLoop 1.0) (1.0 / (1.0 - 0.3) * 2.0 + 1.0)

  putStrLn "direct primitive via run"
  let (yPrim, pbPrim) = runDiff (eval (Circuit.base sq :: Trace (,) Diff' Double Double)) 3.0
  assert "value" yPrim 9.0
  assert "gradient" (pbPrim 1.0) 6.0

  putStrLn "NumHask Multiplicative instance (id * id)"
  let (y1, pb1) = runDiff (id * id :: Diff' Double Double) 3.0
  assert "value" y1 9.0
  assert "gradient" (pb1 1.0) 6.0

  putStrLn "NumHask polynomial (2x^2 + 3x + 5)"
  let poly = constD 2 * id * id + constD 3 * id + constD 5 :: Diff' Double Double
      (y2, pb2) = runDiff poly 1.0
  assert "value" y2 10.0
  assert "gradient" (pb2 1.0) 7.0

  putStrLn "NumHask ExpField instance (exp)"
  let (y3, pb3) = runDiff (exp id :: Diff' Double Double) 0.0
  assert "value" y3 1.0
  assert "gradient" (pb3 1.0) 1.0

  putStrLn "NumHask TrigField instance (sin)"
  let (y4, pb4) = runDiff (sin id :: Diff' Double Double) 0.0
  assert "value" y4 0.0
  assert "gradient" (pb4 1.0) 1.0

  putStrLn "NumHask Divisive instance (recip)"
  let (y5, pb5) = runDiff (recip id :: Diff' Double Double) 2.0
  assert "value" y5 0.5
  assert "gradient" (pb5 1.0) (-0.25)

  putStrLn "Trace Diff Either (scale-by-n loop)"
  let scaleByN n = trace body
        where
          body :: Diff' (Either (Int, Double, Double) Double) (Either (Int, Double, Double) Double)
          body = Diff $ \case
            Right x -> (Left (n, 0, x), \case Left (_, _, dx) -> Right dx; Right _ -> error "scaleByN: unexpected Right cotangent")
            Left (i, acc, x)
              | i <= 0 -> (Right acc, \case Right dc -> Left (0, dc, 0); Left _ -> error "scaleByN: unexpected Left cotangent")
              | otherwise -> (Left (i - 1, acc + x, x), \case Left (_, dacc, dx) -> Left (0, dacc, dx + dacc); Right _ -> error "scaleByN: unexpected Right cotangent")
      (y6, pb6) = runDiff (scaleByN 5) 2.0
  assert "value" y6 10.0
  assert "gradient" (pb6 1.0) 5.0

  putStrLn "Par-interior body trace preserved"
  -- The body has zero channel self-coupling in the feedback wire,
  -- so the lazy 'Trace' knot converges without a forward seed.
  let innerBody =
        Diff
          ( \(x, b) ->
              ((0.0, x + 2.0 * b), \(_, dc) -> (dc, 2.0 * dc))
          ) ::
          Diff' (Double, Double) (Double, Double)
      netBody = Body $ Diff $ \(s, (x, b)) ->
        let (ySq, sqPb) = runDiff sq x
            ((s', o), innerPb) = runDiff innerBody (s, b)
            pb (ds, (dy, do_)) =
              let dx = sqPb dy
                  (dsIn, db) = innerPb (ds, do_)
               in (dsIn, (dx, db))
         in ((s', (ySq, o)), pb)
      (y7, g7) = linearizeBody netBody (3.0, 4.0)
      (_, (gx, gb)) = runPullback (morphism g7) (0.0, (1.0, 1.0))
  assert "value fst" (fst y7) 9.0
  assert "value snd" (snd y7) 8.0
  assert "gradient x" gx 6.0
  assert "gradient b" gb 2.0

  runMatrixStarTests
  runStarEliminateTests
  runTagTests
  runMetricAdjointTests
  runKeplerTests
  runDiffCarrierTests
  runOperatorTests
  runStreamTowerTests
  runTensorTests
