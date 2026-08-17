{-# LANGUAGE RebindableSyntax #-}

-- | Geodesic flow on the polar chart as an ODE spike.
--
-- The geodesic equation in coordinates is
--
-- > d²xⁱ/dt² + Γⁱⱼₖ dxʲ/dt dxᵏ/dt = 0
--
-- which we rewrite as a first-order system
--
-- > dx/dt = v
-- > dvⁱ/dt = -Γⁱⱼₖ vʲ vᵏ.
--
-- The Christoffel symbols come from 'Circuit.Diff.Chart.christoffel2D' applied
-- to the polar metric, so this is a direct integration of the
-- Levi-Civita connection computed by automatic differentiation.
module GeodesicFlow
  ( runGeodesicFlowTests,
  )
where

import Circuit.Diff.Chart
  ( christoffel2D,
    polarMetricLower,
    polarMetricRaise,
  )
import NumHask.Prelude
import Prelude ()

-- | Explicit tuple arithmetic for the 2-D state.
tadd :: (Double, Double) -> (Double, Double) -> (Double, Double)
tadd (a, b) (c, d) = (a + c, b + d)

tscale :: Double -> (Double, Double) -> (Double, Double)
tscale s (a, b) = (s * a, s * b)

-- | Acceleration along a geodesic: @aⁱ = -Γⁱⱼₖ vʲ vᵏ@.
geodesicAcceleration :: (Double, Double) -> (Double, Double) -> (Double, Double)
geodesicAcceleration x v =
  let (g000, g001, g010, g011, g100, g101, g110, g111) =
        christoffel2D polarMetricLower polarMetricRaise x
      (v0, v1) = v
      a0 = negate (g000 * v0 * v0 + g001 * v0 * v1 + g010 * v1 * v0 + g011 * v1 * v1)
      a1 = negate (g100 * v0 * v0 + g101 * v0 * v1 + g110 * v1 * v0 + g111 * v1 * v1)
   in (a0, a1)

-- | First-order dynamics @(x, v) ↦ (v, a)@.
geodesicDynamics ::
  ((Double, Double), (Double, Double)) ->
  ((Double, Double), (Double, Double))
geodesicDynamics (x, v) = (v, geodesicAcceleration x v)

-- | One RK4 step for a first-order ODE on tuples.
rk4Step ::
  Double ->
  ((Double, Double), (Double, Double)) ->
  ((Double, Double), (Double, Double))
rk4Step h (x, v) =
  let k1x = v
      k1v = geodesicAcceleration x v
      k2x = tadd v (tscale (h / 2.0) k1v)
      k2v = geodesicAcceleration (tadd x (tscale (h / 2.0) k1x)) (tadd v (tscale (h / 2.0) k1v))
      k3x = tadd v (tscale (h / 2.0) k2v)
      k3v = geodesicAcceleration (tadd x (tscale (h / 2.0) k2x)) (tadd v (tscale (h / 2.0) k2v))
      k4x = tadd v (tscale h k3v)
      k4v = geodesicAcceleration (tadd x (tscale h k3x)) (tadd v (tscale h k3v))
      x' = tadd x (tscale (h / 6.0) (tadd (tadd k1x (tscale 2.0 k2x)) (tadd (tscale 2.0 k3x) k4x)))
      v' = tadd v (tscale (h / 6.0) (tadd (tadd k1v (tscale 2.0 k2v)) (tadd (tscale 2.0 k3v) k4v)))
   in (x', v')

-- | Integrate for @n@ steps of size @h@.
integrate :: Int -> Double -> ((Double, Double), (Double, Double)) -> ((Double, Double), (Double, Double))
integrate n h = nth n . iterate (rk4Step h)
  where
    nth 0 (y : _) = y
    nth m (_ : ys) = nth (m - 1) ys
    nth _ [] = error "integrate: empty list"

-- | Polar-coordinate speed squared: @gᵢⱼ vⁱ vʲ = (vʳ)² + r² (vᶿ)²@.
speedSquared :: (Double, Double) -> (Double, Double) -> Double
speedSquared (r, _) (vr, vtheta) = vr * vr + r * r * vtheta * vtheta

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Bool -> IO ()
assert name ok =
  if ok
    then putStrLn $ "  PASS " ++ name
    else error $ "FAIL " ++ name

runGeodesicFlowTests :: IO ()
runGeodesicFlowTests = do
  putStrLn "geodesic flow: radial motion is exact"
  let x0 = (1.0, 0.0)
      v0 = (0.5, 0.0)
      h = 0.01
      n = 100
      tFinal = fromIntegral n * h
      ((r, theta), (vr, vtheta)) = integrate n h (x0, v0)
  assert "r(t) = r0 + v0*t" (near r (1.0 + 0.5 * tFinal))
  assert "theta(t) = theta0" (near theta 0.0)
  assert "v^r preserved" (near vr 0.5)
  assert "v^theta stays zero" (near vtheta 0.0)

  putStrLn "geodesic flow: speed is conserved"
  let x1 = (2.0, 0.7)
      v1 = (0.3, 0.4)
      s0 = speedSquared x1 v1
      (xFinal, vFinal) = integrate 200 0.01 (x1, v1)
      sFinal = speedSquared xFinal vFinal
  assert "speed squared conserved" (near s0 sFinal)

  putStrLn "geodesic flow: straight-line oracle in Cartesian"
  -- A geodesic of the Euclidean plane starting at (r=1, theta=0) with
  -- velocity (0, 1) is the vertical line x = 1.  In polar coordinates
  -- this means r*cos(theta) = 1.
  let x2 = (1.0, 0.0)
      v2 = (0.0, 1.0)
      n2 = 500
      h2 = 0.002
      ((r2, theta2), _) = integrate n2 h2 (x2, v2)
      t2 = fromIntegral n2 * h2
      -- Geodesic is the vertical line x = 1.  Arc-length parameterisation
      -- gives (x, y) = (1, t), hence r = sqrt(1 + t^2) and theta = atan t.
      expectedR = sqrt (1.0 + t2 * t2)
      expectedTheta = atan t2
  assert "r matches straight-line" (near r2 expectedR)
  assert "theta matches straight-line" (near theta2 expectedTheta)
