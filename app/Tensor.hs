{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}

module Tensor (runTensorTests) where

import Circuit.Diff (runDiff)
import Circuit.Diff.Array
  ( elementwiseTower,
    matMulD,
    sigmoidD,
    tanhD,
    tensorTaylor,
  )
import Circuit.Diff.Jet (Jet (..), variable)
import Circuit.Mat.Square (Square)
import Data.Foldable (foldl')
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, natVal)
import Harpie.Fixed (Array)
import Harpie.Fixed qualified as F
import Harpie.Shape (KnownNats)
import NumHask.Prelude

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

squareFromLists :: forall n. (KnownNat n) => [[Double]] -> Square n Double
squareFromLists xss = F.array (concat xss)

squareToLists :: forall n. (KnownNat n) => Square n Double -> [[Double]]
squareToLists a =
  let n = fromEnum (natVal (Proxy @n))
   in [[a F.! [i, j] | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]

arraySum :: (KnownNats s) => Array s Double -> Double
arraySum = foldl' (+) zero

nearS :: Double -> Double -> Bool
nearS x y = abs (x - y) < 1e-7

nearFD :: Double -> Double -> Bool
nearFD x y = abs (x - y) < 1e-4

nearM :: forall n. (KnownNat n) => Square n Double -> Square n Double -> Bool
nearM a b =
  let n = fromEnum (natVal (Proxy @n))
   in and [nearS (a F.! [i, j]) (b F.! [i, j]) | i <- [0 .. n - 1], j <- [0 .. n - 1]]

nearMFD :: forall n. (KnownNat n) => Square n Double -> Square n Double -> Bool
nearMFD a b =
  let n = fromEnum (natVal (Proxy @n))
   in and [nearFD (a F.! [i, j]) (b F.! [i, j]) | i <- [0 .. n - 1], j <- [0 .. n - 1]]

assertS :: String -> Double -> Double -> IO ()
assertS name got expected =
  if nearS got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else error $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected

assertM :: forall n. (KnownNat n) => String -> Square n Double -> Square n Double -> IO ()
assertM name got expected =
  if nearM got expected
    then putStrLn $ "  PASS " ++ name
    else error $ "  FAIL " ++ name ++ "\ngot:\n" ++ show (squareToLists got) ++ "\nexpected:\n" ++ show (squareToLists expected)

assertMFD :: forall n. (KnownNat n) => String -> Square n Double -> Square n Double -> IO ()
assertMFD name got expected =
  if nearMFD got expected
    then putStrLn $ "  PASS " ++ name
    else error $ "  FAIL " ++ name ++ "\ngot:\n" ++ show (squareToLists got) ++ "\nexpected:\n" ++ show (squareToLists expected)

-- ---------------------------------------------------------------------------
-- Tensor Taylor towers
-- ---------------------------------------------------------------------------

-- | Build a Jet that represents the scalar function @t -> t * m@ as a matrix
-- series: coefficients are @[t0 * m, m, 0, ...]@.
scalarSeriesMatrix ::
  forall n.
  (KnownNat n) =>
  Int ->
  Square n Double ->
  Double ->
  Jet (Square n Double)
scalarSeriesMatrix k m t0 =
  Jet (take (k + 1) (fmap (t0 *) m : m : repeat zero))

runTensorTowerTests :: IO ()
runTensorTowerTests = do
  putStrLn "tensor tower: elementwise cube"
  let a = squareFromLists @2 [[2.0, 3.0], [-1.5, 4.0]] :: Square 2 Double
      t0 = 1.7
      pt = fmap (t0 *) a
      cube x = x * x * x
      -- h(t) = sum (map (^3) (t * a)); check one component's derivatives.
      a00 = a F.! [0, 0]
      x00 = t0 * a00
      ref =
        [ x00 * x00 * x00,
          3.0 * x00 * x00,
          6.0 * x00,
          6.0,
          0.0
        ]
      coeffs =
        [ elementwiseTower cube k pt F.! [0, 0]
        | k <- [0 .. 4]
        ]
  mapM_ (\(k, (got, expc)) -> assertS ("cube d" ++ show k) got expc) (zip [0 :: Int ..] (zip coeffs ref))

  putStrLn "tensor tower: matmul chain"
  let a = squareFromLists @2 [[1.0, 2.0], [3.0, 4.0]] :: Square 2 Double
      b = squareFromLists @2 [[5.0, 6.0], [7.0, 8.0]] :: Square 2 Double
      t0 = 1.3
      s = arraySum (a * b)
      ja = scalarSeriesMatrix 4 a t0
      jb = scalarSeriesMatrix 4 b t0
      coeffs = tensorTaylor (\_ -> ja * jb) 4 zero
  assertS "matmul value" (arraySum (coeffs !! 0)) (s * t0 * t0)
  assertS "matmul d1" (arraySum (coeffs !! 1)) (2.0 * s * t0)
  assertS "matmul d2" (arraySum (coeffs !! 2)) (2.0 * s)
  assertS "matmul d3" (arraySum (coeffs !! 3)) 0.0
  assertS "matmul d4" (arraySum (coeffs !! 4)) 0.0

  putStrLn "tensor tower: sigmoid/tanh elementwise"
  let c = squareFromLists @2 [[0.4, -0.7], [1.2, 0.9]] :: Square 2 Double
      t0 = 0.5
      pt = fmap (t0 *) c
      -- compute one component's exact scalar sigmoid derivatives as oracle
      c00 = c F.! [0, 0]
      x00 = t0 * c00
      s0 = 1.0 / (1.0 + exp (-x00))
      sigRef =
        [ s0,
          s0 * (1.0 - s0),
          s0 * (1.0 - s0) * (1.0 - 2.0 * s0),
          s0 * (1.0 - s0) * (1.0 - 6.0 * s0 + 6.0 * s0 * s0)
        ]
      sigmoidJet x = one / (one + exp (negate x))
      sigCoeffs =
        [ elementwiseTower sigmoidJet k pt F.! [0, 0]
        | k <- [0 .. 3]
        ]
  mapM_ (\(k, (got, expc)) -> assertS ("sigmoid d" ++ show k) got expc) (zip [0 :: Int ..] (zip sigCoeffs sigRef))

  putStrLn "tensor tower: tanh elementwise"
  let d = squareFromLists @2 [[0.4, -0.7], [1.2, 0.9]] :: Square 2 Double
      t1 = 0.5
      ptTanh = fmap (t1 *) d
      z00 = ptTanh F.! [0, 0]
      y0 = tanh z00
      tanhRef =
        [ y0,
          1.0 - y0 * y0,
          -(2.0 * y0 * (1.0 - y0 * y0)),
          (1.0 - y0 * y0) * (6.0 * y0 * y0 - 2.0)
        ]
      tanhCoeffs =
        [ elementwiseTower tanh k ptTanh F.! [0, 0]
        | k <- [0 .. 3]
        ]
  mapM_ (\(k, (got, expc)) -> assertS ("tanh d" ++ show k) got expc) (zip [0 :: Int ..] (zip tanhCoeffs tanhRef))

-- ---------------------------------------------------------------------------
-- Reverse-mode tensor primitives
-- ---------------------------------------------------------------------------

runReverseTensorTests :: IO ()
runReverseTensorTests = do
  putStrLn "reverse-mode: matMulD adjoint"
  let a = squareFromLists @2 [[1.0, 2.0], [3.0, 4.0]] :: Square 2 Double
      b = squareFromLists @2 [[5.0, 6.0], [7.0, 8.0]] :: Square 2 Double
      db = squareFromLists @2 [[1.0, 0.0], [0.0, 1.0]] :: Square 2 Double
      (_, pb) = runDiff matMulD (a, b)
      (da, db_) = pb db
      daRef = db * F.transpose b
      dbRef = F.transpose a * db
  assertM "dA = dY B^T" da daRef
  assertM "dB = A^T dY" db_ dbRef

  putStrLn "reverse-mode: sigmoidD vs finite differences"
  let x = squareFromLists @2 [[0.5, -0.3], [1.2, 0.0]] :: Square 2 Double
      h = 1e-5
      (_, pb) = runDiff sigmoidD x
      dx = pb (F.konst 1.0)
      dxFD =
        F.zipWith
          (\xi di -> di / h)
          x
          ( F.zipWith
              (-)
              (fmap (fst . phi . (+ h)) x)
              (fmap (fst . phi) x)
          )
      phi y = let s = 1.0 / (1.0 + exp (-y)) in (s, \d -> d * s * (1.0 - s))
  assertMFD "sigmoid pullback" dx dxFD

  putStrLn "reverse-mode: tanhD vs finite differences"
  let x = squareFromLists @2 [[0.5, -0.3], [1.2, 0.0]] :: Square 2 Double
      h = 1e-5
      (_, pb) = runDiff tanhD x
      dx = pb (F.konst 1.0)
      dxFD =
        F.zipWith
          (\xi di -> di / h)
          x
          ( F.zipWith
              (-)
              (fmap (tanh . (+ h)) x)
              (fmap tanh x)
          )
  assertMFD "tanh pullback" dx dxFD

runTensorTests :: IO ()
runTensorTests = do
  runTensorTowerTests
  runReverseTensorTests
