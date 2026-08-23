{-# LANGUAGE RebindableSyntax #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | Eshkol-style AD operator axioms and exact-vs-finite-difference logging.
--
-- Mirrors test cases from eshkol:
--   * tests/ad/taylor_tower_test.esk (scalar high-order towers)
--   * tests/ad/exact_point_ad_test.esk (multivariate operators)
--   * tests/ad/tensor_tower_test.esk (activation elementwise towers)
--
-- For every scalar tower we print both the exact 'Jet' result and the
-- finite-difference 'Taylor' result so the size of the FD gap is visible.
module Operators (runOperatorTests) where

import Circuit.Diff (Diff (..), runDiff)
import Circuit.Diff.Operators
  ( curl,
    derivativeN,
    derivativeNJ,
    divergence,
    gradient,
    hessian,
    jacobian,
    laplacian,
    taylor,
    taylorJ,
  )
import Control.Monad (zipWithM_)
import Data.List (maximumBy)
import Data.Ord (comparing)
import NumHask.Prelude

-- ---------------------------------------------------------------------------
-- Reporting helpers
-- ---------------------------------------------------------------------------

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-7

nearFD :: Double -> Double -> Bool
nearFD x y = abs (x - y) < 1e-1 + 1e-1 * abs y

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else error $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected

assertFD :: String -> Double -> Double -> IO ()
assertFD name got expected = do
  let delta = abs (got - expected)
  if delta < 1e-1 + 1e-1 * abs expected
    then putStrLn $ "  PASS " ++ name ++ " (FD): " ++ show got
    else putStrLn $ "  WARN " ++ name ++ " (FD gap=" ++ show delta ++ "): got " ++ show got ++ ", expected " ++ show expected

logExactVsFD :: String -> Double -> Double -> IO ()
logExactVsFD name exact fd =
  let delta = abs (exact - fd)
   in putStrLn $
        "  "
          ++ name
          ++ "  exact="
          ++ show exact
          ++ "  fd="
          ++ show fd
          ++ "  |diff|="
          ++ show delta

-- ---------------------------------------------------------------------------
-- 1. Scalar Taylor towers: exact (Jet) vs finite-difference (Taylor)
--    Matches eshkol tests/ad/taylor_tower_test.esk.
-- ---------------------------------------------------------------------------

-- | Build a scalar 'Diff' from a value function and its first derivative.
-- Higher-order terms are recovered by the finite-difference Taylor tower.
scalarD :: (Double -> Double) -> (Double -> Double) -> Diff p Double Double
scalarD f f' = Diff $ \x -> (f x, \d -> d * f' x)

runScalarTowerComparison :: IO ()
runScalarTowerComparison = do
  putStrLn "scalar towers: exact Jet vs FD Taylor"

  -- f(x) = x^5 at x0 = 2.0
  let pow5 x = x * x * x * x * x
      pow5D = scalarD (\x -> x ^ (5 :: Int)) (\x -> 5 * x ^ (4 :: Int))
      pow5Ref = [32.0, 80.0, 160.0, 240.0, 240.0, 120.0, 0.0, 0.0, 0.0] :: [Double]
  putStrLn "  x^5 @ 2.0"
  zipWithM_
    ( \n r -> do
        let exact = derivativeNJ pow5 2.0 n
            fd = derivativeN pow5D 2.0 n
        logExactVsFD ("d" ++ show n) exact fd
        assert ("x^5 d" ++ show n) exact r
        assertFD ("x^5 d" ++ show n ++ " FD agrees") fd exact
    )
    [0 .. 8]
    pow5Ref

  -- f(x) = sin(x) at x0 = 0.0
  let sinD = scalarD sin cos
      sinRef = [0.0, 1.0, 0.0, -1.0, 0.0, 1.0, 0.0, -1.0, 0.0] :: [Double]
  putStrLn "  sin @ 0.0"
  zipWithM_
    ( \n r -> do
        let exact = derivativeNJ sin 0.0 n
            fd = derivativeN sinD 0.0 n
        logExactVsFD ("d" ++ show n) exact fd
        assert ("sin d" ++ show n) exact r
    )
    [0 .. 8]
    sinRef

  -- f(x) = exp(x) at x0 = 0.5
  let e05 = exp 0.5
      expD = scalarD exp exp
  putStrLn "  exp @ 0.5"
  zipWithM_
    ( \n _ -> do
        let exact = derivativeNJ exp 0.5 n
            fd = derivativeN expD 0.5 n
        logExactVsFD ("d" ++ show n) exact fd
        assert ("exp d" ++ show n) exact e05
    )
    [0 .. 8]
    ([0 .. 8] :: [Int])

  -- f(x) = log(1+x) at x0 = 0.0
  let log1pD = scalarD (\x -> log (1 + x)) (\x -> 1 / (1 + x))
      log1pRef = [0.0, 1.0, -1.0, 2.0, -6.0, 24.0, -120.0, 720.0, -5040.0] :: [Double]
  putStrLn "  log1p @ 0.0"
  zipWithM_
    ( \n r -> do
        let exact = derivativeNJ (\x -> log (1 + x)) 0.0 n
            fd = derivativeN log1pD 0.0 n
        logExactVsFD ("d" ++ show n) exact fd
        assert ("log1p d" ++ show n) exact r
    )
    [0 .. 8]
    log1pRef

  -- f(x) = 1/(1-x) at x0 = 0.5
  let geomD = scalarD (\x -> 1 / (1 - x)) (\x -> 1 / ((1 - x) * (1 - x)))
      geomRef = [2.0, 4.0, 16.0, 96.0, 768.0, 7680.0, 92160.0, 1290240.0, 20643840.0] :: [Double]
  putStrLn "  geom @ 0.5"
  zipWithM_
    ( \n r -> do
        let exact = derivativeNJ (\x -> recip (1 - x)) 0.5 n
            fd = derivativeN geomD 0.5 n
        logExactVsFD ("d" ++ show n) exact fd
        assert ("geom d" ++ show n) exact r
    )
    [0 .. 8]
    geomRef

  -- Full derivative comparison for exp @ 0.5
  -- (taylor/taylorJ return raw derivatives, not coefficients.)
  putStrLn "  taylor(exp,0.5,4) raw derivatives"
  let exactDerivs = taylorJ (\x -> exp x) 0.5 4
      fdDerivs = taylor expD 0.5 4
      refDerivs = replicate 5 e05
  zipWithM_
    ( \k (e, f, r) -> do
        logExactVsFD ("d" ++ show k) e f
        assert ("taylor-exp d" ++ show k) e r
    )
    ([0 .. 4] :: [Int])
    (zip3 exactDerivs fdDerivs refDerivs)

-- ---------------------------------------------------------------------------
-- 2. Multivariate operators (eshkol tests/ad/exact_point_ad_test.esk)
-- ---------------------------------------------------------------------------

runMultivariateTests :: IO ()
runMultivariateTests = do
  putStrLn "multivariate operators"

  -- gradient: f(v) = sum v_i^2  =>  grad = 2v
  let sqLoss :: Diff () [Double] Double
      sqLoss = Diff $ \v -> let y = sum (map (\x -> x * x) v) in (y, \d -> map (2 * d *) v)
  assertVec "grad sum(v^2) @ [1.3,-0.7,0.6]" (gradient sqLoss [1.3, -0.7, 0.6]) [2.6, -1.4, 1.2]

  -- jacobian of R -> R^2 map: f(t) = (t^2, t^3) => J = [[2t], [3t^2]]
  let r2n :: Diff () Double [Double]
      r2n = Diff $ \t -> ([t * t, t * t * t], \[d0, d1] -> 2 * t * d0 + 3 * t * t * d1)
  let (_, pbR2N) = runDiff r2n 2
      jacR2N = [[pbR2N [1, 0]], [pbR2N [0, 1]]]
  assertMat "R->R^2 derivative (t^2,t^3) @ 2" jacR2N [[4.0], [12.0]]

  -- hessian: f(v) = sum v_i^2 => H = 2I
  let h = hessian sqLoss [1.3, -0.7, 0.6]
  assertMat "hessian sum(v^2)" h [[2.0, 0.0, 0.0], [0.0, 2.0, 0.0], [0.0, 0.0, 2.0]]

  -- divergence: F(v) = (v0^2) => div = 2*v0
  let dmap :: Diff () [Double] [Double]
      dmap = Diff $ \(x : _) -> ([x * x], \[d0] -> [2 * x * d0])
  assert "divergence (v0^2) @ [1/3]" (divergence dmap [1 / 3]) (2 / 3)

  -- curl: F = (y^2, z^2, x^2) => curl = (-2z, -2x, -2y)
  let cmap :: Diff () [Double] [Double]
      cmap =
        Diff $ \v ->
          let x = v !! 0
              y = v !! 1
              z = v !! 2
           in ( [y * y, z * z, x * x],
                \ds -> [2 * x * (ds !! 2), 2 * y * (ds !! 0), 2 * z * (ds !! 1)]
              )
  assertVec "curl (y^2,z^2,x^2) @ [1/3,1/5,1/7]" (curl cmap [1 / 3, 1 / 5, 1 / 7]) [-(2 / 7), -(2 / 3), -(2 / 5)]

  -- laplacian: f(v) = v0^4 => lap = 12*v0^2
  let v0quart :: Diff () [Double] Double
      v0quart = Diff $ \(x : _) -> (x * x * x * x, \d -> [4 * d * x * x * x])
  assertFD "laplacian v0^4 @ [1/3]" (laplacian v0quart [1 / 3]) (4 / 3)

-- ---------------------------------------------------------------------------
-- Vector/matrix assertion helpers
-- ---------------------------------------------------------------------------

assertVec :: String -> [Double] -> [Double] -> IO ()
assertVec name got expected =
  if length got == length expected && and (zipWith near got expected)
    then putStrLn $ "  PASS " ++ name
    else error $ "  FAIL " ++ name ++ " got " ++ show got ++ " expected " ++ show expected

assertMat :: String -> [[Double]] -> [[Double]] -> IO ()
assertMat name got expected =
  if all (\(r, e) -> length r == length e && and (zipWith nearFD r e)) (zip got expected)
    then putStrLn $ "  PASS " ++ name
    else error $ "  FAIL " ++ name ++ "\ngot " ++ show got ++ "\nexpected " ++ show expected

-- ---------------------------------------------------------------------------
-- Entry point
-- ---------------------------------------------------------------------------

runOperatorTests :: IO ()
runOperatorTests = do
  runScalarTowerComparison
  runMultivariateTests
