{-# LANGUAGE RebindableSyntax #-}

-- | Kepler's equation as a fixed-point knot.
--
-- Kepler's equation relates mean anomaly @M@, eccentric anomaly @E@, and
-- eccentricity @e@:
--
-- > E = M + e · sin E
--
-- Solving for @E@ is a scalar fixed-point problem.  The 'Trace' instance for
-- 'Diff ties exactly this knot, and 'traceStarFromD' solves the backward
-- affine equation in closed form via @(I − h·Df)⁻¹@.
module Kepler
  ( runKeplerTests,
  )
where

import Circuit.Diff.Circuit (Diff (..), Diff', runDiff, traceNFrom)
import Circuit.Diff.Star (traceStarFromD)
import NumHask.Prelude
import Prelude ()

-- | Kepler fixed-point body.
--
-- Channel carries the current eccentric anomaly @E@; input is @(M, e)@;
-- output is the updated @E@.
keplerBody :: Diff' (Double, (Double, Double)) (Double, Double)
keplerBody = Diff $ \(eChan, (m, ecc)) ->
  let e' = m + ecc * sin eChan
      deDeChan = ecc * cos eChan
   in ( (e', e'),
        \(dChan, dOut) ->
          let dTotal = dChan + dOut
           in ( dTotal * deDeChan,
                (dTotal, dTotal * sin eChan)
              )
      )

-- | Solve Kepler's equation using the closed-form 'trace' star.
--
-- For @e < 1@ the channel self-coupling @e·cos E@ has magnitude less than one,
-- so the Neumann series / star exists.
solveKeplerStar :: Int -> Diff' (Double, Double) Double
solveKeplerStar n = traceStarFromD 0.0 n keplerBody

-- | Solve Kepler's equation using truncated fixed-point iteration.
solveKeplerN :: Int -> Diff' (Double, Double) Double
solveKeplerN n = traceNFrom 0.0 n keplerBody

-- | Direct Newton solver, used as an oracle.
newtonKepler :: Double -> Double -> Double -> Double
newtonKepler tol m ecc = go 0.0
  where
    go e =
      let f = e - ecc * sin e - m
          fp = 1 - ecc * cos e
          e' = e - f / fp
       in if abs (e' - e) < tol then e' else go e'

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else error $ "FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected

runKeplerTests :: IO ()
runKeplerTests = do
  putStrLn "Kepler equation: trace star vs Newton"
  let m = 1.0
      ecc = 0.5
      n = 30
      ref = newtonKepler 1e-12 m ecc
      (eStar, pbStar) = runDiff (solveKeplerStar n) (m, ecc)
      (eN, pbN) = runDiff (solveKeplerN n) (m, ecc)
  assert "star value" eStar ref
  assert "N-iteration value" eN ref

  putStrLn "Kepler equation: AD derivative vs analytic"
  -- dE/dM = 1 / (1 - e·cos E)
  let analyticDE :: Double -> Double -> Double
      analyticDE dM _dE = dM / (1 - ecc * cos ref)
      (dMStar, _dEccStar) = pbStar 1.0
  assert "dE/dM (star)" dMStar (analyticDE 1.0 0.0)
  assert "dE/dM (N)" (fst (pbN 1.0)) (analyticDE 1.0 0.0)
  -- dE/de = sin E / (1 - e·cos E)
  let (_, dEccStar') = pbStar 1.0
  assert "dE/de (star)" dEccStar' (sin ref / (1 - ecc * cos ref))

  putStrLn "Kepler equation: high-eccentricity orbit"
  let m2 = 2.0
      ecc2 = 0.9
      ref2 = newtonKepler 1e-12 m2 ecc2
      (eStar2, _) = runDiff (solveKeplerStar 200) (m2, ecc2)
      (eN2, _) = runDiff (solveKeplerN 200) (m2, ecc2)
  assert "star value at e=0.9" eStar2 ref2
  assert "N-iteration value at e=0.9" eN2 ref2
