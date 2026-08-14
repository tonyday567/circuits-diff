{-# LANGUAGE RebindableSyntax #-}

-- | Differential-geometric oracles built on jets.
--
-- This module specialises to computable cases first: surfaces of revolution
-- need only a 1-D jet in the profile height, while the full metric/Christoffel
-- form is kept for later generalisation.
module Circuit.Diff.Curvature.Surface
  ( surfaceOfRevolutionK,
  )
where

import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Field (ExpField (..))
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Data.Integral (FromInteger (..))
import Circuit.Diff.Jet (Jet, taylor)
import Prelude hiding (fromInteger, negate, recip, sqrt, (*), (+), (-), (/))
import Prelude qualified as P

-- | Gaussian curvature of a surface of revolution @r = f(z)@ at height @z@.
--
-- For a profile curve rotated around the @z@-axis the metric is
-- @ds² = (1 + f'(z)²) dz² + f(z)² dθ²@, giving
-- @K = -f''(z) / (f(z) · (1 + f'(z)²)²)@.
--
-- Oracle: the unit sphere has profile @r = sqrt(1 - z²)@ and @K = 1@.
surfaceOfRevolutionK ::
  (ExpField a, FromInteger a) =>
  (Jet a -> Jet a) ->
  a ->
  a
surfaceOfRevolutionK f z =
  let ds = taylor f 2 z
      fz = ds P.!! 0
      fp = ds P.!! 1
      fpp = ds P.!! 2
      denom = fz * (one + fp * fp) * (one + fp * fp)
   in negate fpp / denom
