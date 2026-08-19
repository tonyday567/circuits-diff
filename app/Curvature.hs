{-# LANGUAGE RebindableSyntax #-}

-- | End-to-end curvature oracles (Albert arXiv:2312.02664 style).
--
-- 1. Flat polar plane: Riemann vanishes (coordinate curvature only).
-- 2. Unit 2-sphere: Ricci scalar = 2.
-- 3. Schwarzschild exterior: vacuum Ricci R_μν = 0 (Einstein LHS for T=0).
module Curvature
  ( runCurvatureTests,
  )
where

import Circuit.Diff.Chart
  ( polarMetricLower,
    polarMetricRaise,
  )
import Circuit.Diff.Curvature
  ( ricci2D,
    ricciDiagonal,
    ricciScalar2D,
    riemann2D,
    schwarzschildMetric,
    sphereMetricLower,
    sphereMetricRaise,
  )
import NumHask.Prelude
import Prelude ()

nearLoose :: Double -> Double -> Bool
nearLoose x y = abs (x - y) < 1.0e-4

assertLoose :: String -> Double -> Double -> IO ()
assertLoose name got expected =
  if nearLoose got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else do
      putStrLn $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected
      error "curvature test failed"

assertSmall :: String -> Double -> IO ()
assertSmall name got =
  if abs got < 1.0e-4
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got ++ " ≈ 0"
    else do
      putStrLn $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected ≈ 0"
      error "curvature test failed"

runCurvatureTests :: IO ()
runCurvatureTests = do
  putStrLn "curvature: flat polar plane has vanishing Riemann"
  let r = 2.0
      theta = pi / 6
      x = (r, theta)
      -- sample independent components (antisym in last pair, etc.)
      comps =
        [ (rho, sigma, mu, nu)
        | rho <- [0, 1],
          sigma <- [0, 1],
          mu <- [0, 1],
          nu <- [0, 1],
          mu < nu
        ]
  mapM_
    ( \(rho, sigma, mu, nu) ->
        assertSmall
          ("R^" ++ show rho ++ "_{" ++ show sigma ++ show mu ++ show nu ++ "}")
          (riemann2D polarMetricLower polarMetricRaise x rho sigma mu nu)
    )
    comps
  assertSmall "Ricci scalar (flat polar)" (ricciScalar2D polarMetricLower polarMetricRaise x)

  putStrLn "curvature: unit 2-sphere Ricci scalar = 2"
  -- Avoid poles (θ=0) and equator singularities in chart; use θ=π/3.
  let th = pi / 3
      ph = 0.4
      xsph = (th, ph)
      rScalar = ricciScalar2D sphereMetricLower sphereMetricRaise xsph
  assertLoose "R (unit sphere)" rScalar 2.0
  -- Ricci diagonal: R_θθ = 1, R_φφ = sin²θ
  assertLoose
    "R_θθ"
    (ricci2D sphereMetricLower sphereMetricRaise xsph 0 0)
    1.0
  assertLoose
    "R_φφ"
    (ricci2D sphereMetricLower sphereMetricRaise xsph 1 1)
    (sin th * sin th)

  putStrLn "curvature: Schwarzschild exterior vacuum Ricci ≈ 0"
  -- M = 1 ⇒ rs = 2; evaluate at r = 10, θ = π/3 (outside horizon).
  let rs = 2.0
      m = schwarzschildMetric rs
      pt = [0.0, 10.0, pi / 3, 0.5]
  mapM_
    ( \(s, n) ->
        assertSmall
          ("R_{" ++ show s ++ show n ++ "}")
          (ricciDiagonal m pt s n)
    )
    [(s, n) | s <- [0 .. 3], n <- [0 .. 3], s <= n]
