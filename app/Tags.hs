{-# LANGUAGE RebindableSyntax #-}

-- | Tests for phantom-tag separation on 'Diff'.
module Tags
  ( runTagTests,
  )
where

import Circuit.Diff.Circuit (Diff (..), Diff', runDiff)
import NumHask.Prelude

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else error $ "FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected

-- | Two distinct phantom tags.  They have no runtime representation; their
-- only purpose is to keep different invocations of AD from mixing.
data Tag1

data Tag2

-- | A tagged differentiable map.
sqrTag1 :: Diff Tag1 Double Double
sqrTag1 = Diff (\x -> (x * x, \d -> 2 * x * d))

-- | Another map with the same tag composes cleanly.
incTag1 :: Diff Tag1 Double Double
incTag1 = Diff (\x -> (x + 1, id))

runTagTests :: IO ()
runTagTests = do
  putStrLn "Phantom tag composition and numeric results"
  let f = incTag1 . sqrTag1
      (y, pb) = runDiff f 3.0
  assert "tagged value" y 10.0
  assert "tagged gradient" (pb 1.0) 6.0

  putStrLn "Untagged Diff behaves identically to tagged Diff"
  let sqrUntagged = Diff (\x -> (x * x, \d -> 2 * x * d)) :: Diff' Double Double
      incUntagged = Diff (\x -> (x + 1, id)) :: Diff' Double Double
      (yU, pbU) = runDiff (incUntagged . sqrUntagged) 3.0
  assert "untagged value" yU 10.0
  assert "untagged gradient" (pbU 1.0) 6.0

  putStrLn "Nested-AD shapes compile (outer Diff operates over inner Diff values)"
  -- The inner arrow is a Diff Tag1 Double Double.  The outer arrow is a
  -- Diff Tag2 (inner) (inner).  Because the inner type carries its own tag,
  -- the outer perturbation cannot be confused with the inner one.
  let inner :: Diff Tag1 Double Double
      inner = Diff (\x -> (x * x, \d -> 2 * x * d))
      outer :: Diff Tag2 (Diff Tag1 Double Double) (Diff Tag1 Double Double)
      outer = Diff (\z -> (z * z, \dz -> z * dz + dz * z))
      (result, _pb) = runDiff outer inner
      (primal, _) = runDiff result 2.0
  assert "nested primal" primal 16.0
