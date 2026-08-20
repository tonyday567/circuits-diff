{-# LANGUAGE LambdaCase #-}

-- | Tiny Newton / linear-solve utilities for differentiable systems.
module Circuit.Diff.Newton
  ( solve2,
  )
where

import Prelude

-- | Solve a 2×2 linear system.
--
-- For a system @A x = b@ with @A = [[a,b],[c,d]]@ and @b = [r,s]@,
-- returns @x@ using Cramer's rule.  If the determinant is near zero,
-- returns a zero vector as a soft failure.
solve2 :: [[Double]] -> [Double] -> [Double]
solve2 [[a, b], [c, d]] [r, s] =
  let det = a * d - b * c
   in if abs det < 1e-14
        then [0, 0]
        else [(d * r - b * s) / det, (a * s - c * r) / det]
solve2 _ _ = error "solve2: expected 2×2"
