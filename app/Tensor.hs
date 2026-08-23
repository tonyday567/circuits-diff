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
  let a2 = squareFromLists @2 [[1.0, 2.0], [3.0, 4.0]] :: Square 2 Double
      b2 = squareFromLists @2 [[5.0, 6.0], [7.0, 8.0]] :: Square 2 Double
      t02 = 1.3
      s2 = arraySum (a2 * b2)
      ja2 = scalarSeriesMatrix 4 a2 t02
      jb2 = scalarSeriesMatrix 4 b2 t02
      coeffs2 = tensorTaylor (\_ -> ja2 * jb2) 4 zero
  assertS "matmul value" (arraySum (coeffs2 !! 0)) (s2 * t02 * t02)
  assertS "matmul d1" (arraySum (coeffs2 !! 1)) (2.0 * s2 * t02)
  assertS "matmul d2" (arraySum (coeffs2 !! 2)) (2.0 * s2)
  assertS "matmul d3" (arraySum (coeffs2 !! 3)) 0.0
  assertS "matmul d4" (arraySum (coeffs2 !! 4)) 0.0

  putStrLn "tensor tower: sigmoid/tanh elementwise"
  let c2 = squareFromLists @2 [[0.4, -0.7], [1.2, 0.9]] :: Square 2 Double
      t03 = 0.5
      pt2 = fmap (t03 *) c2
      -- compute one component's exact scalar sigmoid derivatives as oracle
      c00_2 = c2 F.! [0, 0]
      x00_2 = t03 * c00_2
      s0 = 1.0 / (1.0 + exp (-x00_2))
      sigRef =
        [ s0,
          s0 * (1.0 - s0),
          s0 * (1.0 - s0) * (1.0 - 2.0 * s0),
          s0 * (1.0 - s0) * (1.0 - 6.0 * s0 + 6.0 * s0 * s0)
        ]
      sigmoidJet x = one / (one + exp (negate x))
      sigCoeffs2 =
        [ elementwiseTower sigmoidJet k pt2 F.! [0, 0]
        | k <- [0 .. 3]
        ]
  mapM_ (\(k, (got, expc)) -> assertS ("sigmoid d" ++ show k) got expc) (zip [0 :: Int ..] (zip sigCoeffs2 sigRef))

  putStrLn "tensor tower: tanh elementwise"
  let d2 = squareFromLists @2 [[0.4, -0.7], [1.2, 0.9]] :: Square 2 Double
      t12 = 0.5
      ptTanh2 = fmap (t12 *) d2
      z00_2 = ptTanh2 F.! [0, 0]
      y0 = tanh z00_2
      tanhRef =
        [ y0,
          1.0 - y0 * y0,
          -(2.0 * y0 * (1.0 - y0 * y0)),
          (1.0 - y0 * y0) * (6.0 * y0 * y0 - 2.0)
        ]
      tanhCoeffs2 =
        [ elementwiseTower tanh k ptTanh2 F.! [0, 0]
        | k <- [0 .. 3]
        ]
  mapM_ (\(k, (got, expc)) -> assertS ("tanh d" ++ show k) got expc) (zip [0 :: Int ..] (zip tanhCoeffs2 tanhRef))

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
  let x2 = squareFromLists @2 [[0.5, -0.3], [1.2, 0.0]] :: Square 2 Double
      h2 = 1e-5
      (_, pb2) = runDiff sigmoidD x2
      dx2 = pb2 (F.konst 1.0)
      dxFD2 =
        F.zipWith
          (\_ di -> di / h2)
          x2
          ( F.zipWith
              (-)
              (fmap (fst . phi . (+ h2)) x2)
              (fmap (fst . phi) x2)
          )
      phi y = let s = 1.0 / (1.0 + exp (-y)) in (s, \d -> d * s * (1.0 - s))
  assertMFD "sigmoid pullback" dx2 dxFD2

  putStrLn "reverse-mode: tanhD vs finite differences"
  let x3 = squareFromLists @2 [[0.5, -0.3], [1.2, 0.0]] :: Square 2 Double
      h3 = 1e-5
      (_, pb3) = runDiff tanhD x3
      dx3 = pb3 (F.konst 1.0)
      dxFD3 =
        F.zipWith
          (\_ di -> di / h3)
          x3
          ( F.zipWith
              (-)
              (fmap (tanh . (+ h3)) x3)
              (fmap tanh x3)
          )
  assertMFD "tanh pullback" dx3 dxFD3

runTensorTests :: IO ()
runTensorTests = do
  runTensorTowerTests
  runReverseTensorTests
