{-# LANGUAGE RebindableSyntax #-}

-- | Carrier-level oracles for jets, inverse functions, RDC axioms, and
-- surface-of-revolution curvature.  These originally lived in @numhask-diff@.
module DiffCarrierTests
  ( runDiffCarrierTests,
  )
where

import Circuit.Diff (Diff)
import Circuit.Diff.Inverse (constDiff, implicit1N, inverseN, varDiff)
import Circuit.Diff.Jet (taylor)
import Circuit.Diff.RDC
  ( rdcAdditive,
    rdcChain,
    rdcFst,
    rdcHomogeneous,
    rdcIdentity,
    rdcLinear,
    rdcMixedPartials,
    rdcPairing,
    rdcSnd,
    rdcTerminal,
  )
import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Field (ExpField, TrigField)
import NumHask.Algebra.Field qualified as NHField
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import System.Exit (exitFailure)
import NumHask.Prelude

eps :: Double
eps = 1e-10

assert :: String -> Bool -> IO ()
assert msg ok =
  if ok
    then putStrLn ("  PASS " ++ msg)
    else do
      putStrLn ("  FAIL " ++ msg)
      exitFailure

near :: [Double] -> [Double] -> Bool
near xs ys =
  length xs == length ys && all (\(x, y) -> abs (x - y) < eps) (zip xs ys)

runDiffCarrierTests :: IO ()
runDiffCarrierTests = do
  putStrLn "Jet oracle tests"

  assert "exp at 0" $
    taylor NHField.exp 5 (0.0 :: Double) `near` [1.0, 1.0, 1.0, 1.0, 1.0, 1.0]

  assert "sin at 0" $
    taylor NHField.sin 7 (0.0 :: Double) `near` [0.0, 1.0, 0.0, -1.0, 0.0, 1.0, 0.0, -1.0]

  assert "cos at 0" $
    taylor NHField.cos 7 (0.0 :: Double) `near` [1.0, 0.0, -1.0, 0.0, 1.0, 0.0, -1.0, 0.0]

  assert "log at 1" $
    taylor NHField.log 5 (1.0 :: Double) `near` [0.0, 1.0, -1.0, 2.0, -6.0, 24.0]

  assert "exp at 1" $
    let ds = taylor NHField.exp 5 (1.0 :: Double)
        e = NHField.exp 1.0
     in ds `near` [e, e, e, e, e, e]

  assert "composition: exp(sin(x)) at 0" $
    let ds = taylor (NHField.exp . NHField.sin) 5 (0.0 :: Double)
        expected = [1.0, 1.0, 1.0, 0.0, -3.0, -8.0]
     in ds `near` expected

  putStrLn "Inverse / implicit oracle tests"

  let x :: Diff p Double Double
      x = varDiff

  assert "inverse: sqrt via x²" $
    let root = inverseN (x * x) 2.0 1.5 10
     in abs (root - sqrt 2.0) < 1e-12

  assert "inverse: log via exp" $
    let root = inverseN (NHField.exp x) (NHField.exp 1.0) 0.5 10
     in abs (root - 1.0) < 1e-12

  assert "implicit: circle y = sqrt(1 - x²)" $
    let xVal = 0.6 :: Double
        y0 = 0.8 :: Double
        y = varDiff
        g = constDiff xVal * constDiff xVal + y * y - one
        root = implicit1N g y0 10
        expected = sqrt (1.0 - xVal * xVal)
     in abs (root - expected) < 1e-12

  putStrLn "RDC axiom tests"

  assert "RD.1: rdc preserves addition" $
    let f = NHField.exp x
        g = NHField.sin x
     in rdcAdditive eps f g (1.0 :: Double) 1.0 1.0

  assert "RD.2: rdc is linear in cotangent" $
    rdcLinear eps (NHField.exp x) (1.0 :: Double) 0.3 0.5 0.7

  assert "RD.6: rdc is homogeneous in cotangent" $
    rdcHomogeneous eps (NHField.exp x) (1.0 :: Double) 0.5 3.0

  assert "RD.3: rdc of identity" $
    rdcIdentity eps (2.0 :: Double) 1.0

  assert "RD.3: rdc of fst projection" $
    rdcFst eps (2.0 :: Double, 3.0 :: Double) 1.0

  assert "RD.3: rdc of snd projection" $
    rdcSnd eps (2.0 :: Double, 3.0 :: Double) 1.0

  assert "RD.4: rdc of pairing" $
    let f = NHField.exp x
        g = NHField.sin x
     in rdcPairing eps f g (1.0 :: Double) (0.5, 0.7) (0.2, 0.3)

  assert "RD.4: rdc of terminal morphism" $
    rdcTerminal eps (2.0 :: Double)

  assert "RD.5: reverse chain rule" $
    let f = NHField.sin x
        g = NHField.exp (varDiff :: Diff p Double Double)
     in rdcChain eps f g (1.0 :: Double) 1.0

  assert "RD.5: reverse chain rule on polynomial composition" $
    let f = x * x
        g = NHField.exp varDiff
     in rdcChain eps f g (2.0 :: Double) 1.0

  assert "RD.7: symmetry of mixed partials" $
    let f :: (ExpField a, TrigField a) => (a, a) -> a
        f (u, v) = u * u * v + NHField.sin (u * v)
     in rdcMixedPartials eps f (0.7 :: Double, 1.2 :: Double)
