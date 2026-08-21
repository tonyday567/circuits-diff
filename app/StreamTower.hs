-- | Stream-tower oracles.
--
-- The elementary-function recurrences in 'Circuit.Diff.Jet' are now driven by
-- 'Circuit.Process' generators.  This module checks those generators against
-- closed-form reference series, and it checks that a linear tower recurrence
-- agrees coefficient-wise with the 'starMatrix' solution of the same linear
-- knot.
module StreamTower
  ( runStreamTowerTests,
  )
where

import Circuit.Diff.Jet (Jet (..), coefficients, variable)
import Circuit.Mat.Dense (fromLists, matVec, starMatrix)
import NumHask.Algebra.Field (ExpField (..), TrigField (..))
import NumHask.Algebra.Multiplicative (Divisive (recip))
import NumHask.Free.Carriers (FieldStar (..))
import System.Exit (exitFailure)
import Prelude hiding (cos, exp, log, recip, sin, sqrt)
import Prelude qualified as P

eps :: Double
eps = 1e-9

near :: Double -> Double -> Bool
near x y = abs (x - y) < eps

nearList :: [Double] -> [Double] -> Bool
nearList xs ys =
  P.length xs == P.length ys
    && P.all (uncurry near) (P.zip xs ys)

assertList :: String -> [Double] -> [Double] -> IO ()
assertList name got expected =
  if nearList got expected
    then putStrLn $ "  PASS " ++ name
    else do
      putStrLn $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected
      exitFailure

fact :: Int -> Double
fact n = P.fromInteger (P.product [1 .. P.fromIntegral n])

-- | Direct reference implementation of the exp recurrence (the old list style),
-- kept here as an independent oracle for the new process-based generator.
oldExpSeries :: [Double] -> [Double]
oldExpSeries [] = []
oldExpSeries (u0 : us) =
  let n = P.length us
      vs = P.map go [0 .. n]
      go 0 = exp u0
      go m =
        let m' = P.fromInteger (P.toInteger m)
         in (1.0 / m') * sum [P.fromInteger (P.toInteger (m P.- j)) * (vs P.!! j) * (us P.!! (m P.- j P.- 1)) | j <- [0 .. m P.- 1]]
   in vs

-- | Coefficients of exp(a + h): exp(a) / k!
expVariable :: Int -> Double -> [Double]
expVariable n a = [exp a / fact k | k <- [0 .. n]]

-- | k-th derivative of sin at a, divided by k!.
sinVariable :: Int -> Double -> [Double]
sinVariable n a = [sinDeriv k / fact k | k <- [0 .. n]]
  where
    sinDeriv k = case P.mod k 4 of
      0 -> sin a
      1 -> cos a
      2 -> negate (sin a)
      _ -> negate (cos a)

cosVariable :: Int -> Double -> [Double]
cosVariable n a = [cosDeriv k / fact k | k <- [0 .. n]]
  where
    cosDeriv k = case P.mod k 4 of
      0 -> cos a
      1 -> negate (sin a)
      2 -> negate (cos a)
      _ -> sin a

-- | Coefficients of 1/(a + h): (-1)^k / a^(k+1).
recipVariable :: Int -> Double -> [Double]
recipVariable n a = [((-1) ^ k) / (a ^ (k P.+ 1)) | k <- [0 .. n]]

-- | Coefficients of sqrt(a + h) via the binomial series.
sqrtVariable :: Int -> Double -> [Double]
sqrtVariable n a =
  let sa = sqrt a
      binom k = P.product [1 / 2 - P.fromInteger (P.toInteger j) | j <- [0 .. k P.- 1]] / fact k
   in [sa * binom k / (a ^ k) | k <- [0 .. n]]

-- | Fibonacci recurrence as a tower.
fibRec :: Int -> [Double]
fibRec n = go n
  where
    go 0 = [0]
    go 1 = [0, 1]
    go m =
      let prev = go (m P.- 1)
       in prev ++ [prev P.!! (m P.- 1) + prev P.!! (m P.- 2)]

-- | Strictly-lower-triangular companion matrix for the Fibonacci recurrence.
-- Row @i@ (for @i >= 2@) has ones in columns @i-1@ and @i-2@.
fibCompanion :: Int -> [[Double]]
fibCompanion n =
  [ [if i >= 2 && (j == i P.- 1 || j == i P.- 2) then 1.0 else 0.0 | j <- [0 .. n]]
    | i <- [0 .. n]
  ]

runStreamTowerTests :: IO ()
runStreamTowerTests = do
  putStrLn "Stream-tower elementary-function oracles"

  let n = 8
      a = 1.5

  assertList "exp variable matches factorial series" (coefficients (exp (variable n a))) (expVariable n a)
  assertList "sin variable matches derivative series" (coefficients (sin (variable n a))) (sinVariable n a)
  assertList "cos variable matches derivative series" (coefficients (cos (variable n a))) (cosVariable n a)
  assertList "recip variable matches geometric series" (coefficients (recip (variable n a))) (recipVariable n a)
  assertList "sqrt variable matches binomial series" (coefficients (sqrt (variable n a))) (sqrtVariable n a)

  putStrLn "Stream-tower exp pilot (process vs direct reference)"
  let u0 = 0.7 :: Double
      us = [0.3, -0.2, 0.05, 0.01, -0.005]
  assertList "exp generic input" (coefficients (exp (Jet (u0 : us)))) (oldExpSeries (u0 : us))

  putStrLn "GF/star coherence oracle (Fibonacci)"
  let order = 12
      coeffs = fibRec order
      l = fibCompanion order
      b = P.map FieldStar (P.take (order P.+ 1) ([0, 1] ++ P.repeat 0))
      mat = fromLists (P.map (P.map FieldStar) l)
      solved = P.map (\(FieldStar x) -> x) (matVec (starMatrix mat) b)
  assertList "starMatrix solves Fibonacci recurrence" solved coeffs
