-- | Oracles for 'Circuit.Diff.DubinsChase'
-- (deck 0 kinematics, deck 1 soft loss / FD, deck 1b reverse mode, deck 2 optimizers).
module DubinsChase
  ( runDubinsChase,
  )
where

import Circuit.Diff.DubinsChase
import Circuit.Diff (runDiff)
import System.Exit (exitFailure)
import Text.Printf (printf)

assertNear :: String -> Double -> Double -> Double -> IO ()
assertNear name tol got expected =
  if abs (got - expected) < tol
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got ++ " ≈ " ++ show expected
    else do
      putStrLn $
        "  FAIL "
          ++ name
          ++ ": got "
          ++ show got
          ++ ", expected "
          ++ show expected
      exitFailure

assertTrue :: String -> Bool -> IO ()
assertTrue name ok =
  if ok
    then putStrLn $ "  PASS " ++ name
    else do
      putStrLn $ "  FAIL " ++ name
      exitFailure

runDubinsChase :: IO ()
runDubinsChase = do
  putStrLn "=== dubins-chase deck 0: dynamics sanity ==="
  let p = defaultParams
      dt = 0.01
      tEnd = 1.0
      n = round (tEnd / dt) :: Int

  -- Straight line: u = 0, heading 0 → distance ≈ v_p * T
  let straight = rollout p dt (replicate n (0, 0)) ((0, 0, 0), (10, 0))
      (xf, yf, _) = fst (last straight)
      dStraight = sqrt (xf * xf + yf * yf)
  printf "straight: final pursuer (%.4f, %.4f) dist=%.4f\n" xf yf dStraight
  assertNear "straight-line path length" 0.02 dStraight (pSpeed p * tEnd)
  assertNear "straight no lateral drift" 1e-9 yf 0

  -- Full lock left: u = 1 → circle radius R, arc angle v*T/R
  let circ = rollout p dt (replicate n (1, 0)) ((0, 0, 0), (0, 0))
      samples = pursuerPath circ
      (xe, ye) = last samples
      chord = sqrt (xe * xe + ye * ye)
      r = pTurnR p
      ang = pSpeed p * tEnd / r
      chordExact = 2 * r * sin (ang / 2)
  printf "full-lock: chord=%.4f exact=%.4f angle=%.4f rad\n" chord chordExact ang
  assertNear "full-lock turn chord" 0.05 chord chordExact

  -- Capture predicate
  assertTrue "captured at contact" (captured p (0, 0) (0.05, 0))
  assertTrue "not captured far" (not (captured p (0, 0) (1, 0)))

  -- Pure pursuit toward a fixed (stationary) evader: distance shrinks.
  let e0 = (1.0, 0.0)
      pStill = p {eSpeed = 0}
      chase =
        take (n + 1) $
          iterate
            ( \w ->
                let ((px, py, th), (ex, ey)) = w
                    phi = atan2 (ey - py) (ex - px)
                    err = atan2 (sin (phi - th)) (cos (phi - th))
                    u = max (-1) (min 1 (2 * err))
                 in stepWorld pStill dt u 0 w
            )
            ((0, 0, 0), e0)
      d0 = distance (0, 0) e0
      d1 = distance (let (a, b, _) = fst (last chase) in (a, b)) e0
  printf "chase fixed evader: d0=%.4f d1=%.4f\n" d0 d1
  assertTrue "distance decreases toward fixed evader" (d1 < d0 - 0.1)

  putStrLn "=== dubins-chase deck 1: soft loss + FD ==="
  -- Evader flees along +x; pursuer starts offset facing +y, open-loop zero
  -- controls leave a positive soft loss; a short descent should reduce it.
  let wChase = ((0, 0, pi / 2), (0.5, 0)) -- pursuer facing +y, evader to the right
      phis = replicate 40 0 -- evader heads +x
      us0 = replicate 40 0 -- pursuer no turn
      loss0 = lossOfControls p dt us0 phis wChase
      g = gradU_FD p dt 1e-4 us0 phis wChase
      us1 = descendU p dt 1e-4 0.5 us0 phis wChase
      loss1 = lossOfControls p dt us1 phis wChase
  printf "soft loss0=%.6f  loss1=%.6f  |grad|_inf=%.4f\n" loss0 loss1 (maximum (map abs g))
  assertTrue "initial soft loss positive" (loss0 > 1e-3)
  assertTrue "FD grad has some signal" (maximum (map abs g) > 1e-6)
  assertTrue "one descent step reduces soft loss" (loss1 < loss0)

  -- Finite-difference self-consistency: bump one control, directional
  -- derivative ≈ central FD (same formula, different index).
  let usMid = 0 : replicate 39 0
      gMid = gradU_FD p dt 1e-4 usMid phis wChase
      dir = case gMid of
        (g0 : _) -> g0
        [] -> 0
      lossPlus = lossOfControls p dt (clampU 1e-3 : drop 1 usMid) phis wChase
      lossMinus = lossOfControls p dt (clampU (-1e-3) : drop 1 usMid) phis wChase
      dirFD = (lossPlus - lossMinus) / 2e-3
  printf "grad_0=%.6f  re-FD=%.6f\n" dir dirFD
  assertNear "FD self-consistency on u0" 5e-2 dir dirFD

  putStrLn "=== dubins-chase deck 1b: Diff' / DiffP reverse mode ==="
  -- Same scene: reverse-mode on the polymorphic loss must match FD.
  -- Interior controls (zeros) so clamp kink is off the table.
  let gDiff = gradU_Diff p dt us0 phis wChase
      gDiffP = gradU_DiffP p dt us0 phis wChase
      maxAbsDiff =
        maximum
          (zipWith (\a b -> abs (a - b)) gDiff g)
      maxAbsDiffP =
        maximum
          (zipWith (\a b -> abs (a - b)) gDiffP gDiff)
  printf
    "|gradFD|_inf=%.4f  |gradDiff-FD|_inf=%.3e  |gradDiffP-Diff|_inf=%.3e\n"
    (maximum (map abs g))
    maxAbsDiff
    maxAbsDiffP
  assertTrue "Diff' matches FD (inf-norm)" (maxAbsDiff < 1e-4)
  assertTrue "DiffP matches Diff' (inf-norm)" (maxAbsDiffP < 1e-12)
  -- Forward value of reverse-mode loss agrees with Double path.
  let (lossRM, _) = runDiff (lossAsDiff p dt 0 us0 phis wChase) 0
  assertNear "lossAsDiff value = lossOfControls" 1e-12 lossRM loss0

  putStrLn "=== dubins-chase deck 2: open-loop optimizers ==="
  -- Stationary offset target. Objective = min soft loss along path (aligned
  -- with hard capture). Cold-start from zero open-loop u; PP is the baseline.
  let pFix =
        defaultParams
          { eSpeed = 0,
            captureR = 0.2,
            pTurnR = 0.8
          }
      cfg =
        defaultOpt
          { ocDt = 0.05,
            ocMaxIters = 40,
            ocEta0 = 30.0,
            ocEps = 1e-3
          }
      n2 = 60
      phis2 = replicate n2 0
      wOff = ((0, 0, 0), (1.0, 0.4)) :: World
      usZero = replicate n2 0
      usPP = purePursuitU pFix (ocDt cfg) phis2 wOff
      path0 = rollout pFix (ocDt cfg) (zip usZero phis2) wOff
      pathPP = rollout pFix (ocDt cfg) (zip usPP phis2) wOff
      (usOpt, hist) = optimizeU pFix cfg usZero phis2 wOff
      pathOpt = rollout pFix (ocDt cfg) (zip usOpt phis2) wOff
      dZero = minDistancePath path0
      dPP = minDistancePath pathPP
      dOpt = minDistancePath pathOpt
      l0 = lossMinSoft pFix (ocDt cfg) usZero phis2 wOff
      lOpt = case reverse hist of
        (lf : _) -> lf
        [] -> l0
  printf
    "stationary offset: d0=%.4f dPP=%.4f dOpt=%.4f  loss0=%.6f lossOpt=%.6f  steps=%d\n"
    dZero
    dPP
    dOpt
    l0
    lOpt
    (length hist - 1)
  assertTrue "pure pursuit beats zero open-loop (minDist)" (dPP < dZero - 0.05)
  assertTrue "pure pursuit captures (stationary baseline)" (everCaptured pFix pathPP)
  assertTrue "multi-step opt cuts min-soft loss from zero" (lOpt < l0 * 0.5 || lOpt < 1e-8)
  assertTrue "multi-step opt improves minDist vs zero" (dOpt < dZero - 0.05)
  assertTrue "optimizer reaches hard capture from zero" (everCaptured pFix pathOpt)

  -- Deck-1 honesty: one projected step on path-mean is weak; multi-step
  -- min-soft from zero must land lower than a single path-mean step.
  let usOne = descendU pFix (ocDt cfg) (ocEps cfg) 0.5 usZero phis2 wOff
      lOneMin = lossMinSoft pFix (ocDt cfg) usOne phis2 wOff
  printf "one-step min-soft=%.6f  multi-step min-soft=%.6f\n" lOneMin lOpt
  assertTrue "multi-step beats one-step min-soft" (lOpt < lOneMin)

  -- Speed-ratio sweep (public geometry, not a book holdout).
  -- Higher ν = faster fleer → harder on a fixed open-loop flee heading.
  let pBase = defaultParams {captureR = 0.2, pTurnR = 0.8}
      cfgSw =
        defaultOpt
          { ocDt = 0.05,
            ocMaxIters = 40,
            ocEta0 = 25.0,
            ocEps = 1e-3
          }
      nSw = 50
      phisFlee = replicate nSw (pi / 2) -- flee +y
      wChase2 = ((0, 0, 0), (0.5, 0.2)) :: World
      usWarm = replicate nSw 0
      rows = sweepSpeedRatio pBase cfgSw [0.0, 0.3, 0.6] phisFlee wChase2 usWarm
  mapM_
    ( \(nu, d, cap) ->
        printf "  sweep ν=%.2f  minDist=%.4f  captured=%s\n" nu d (show cap)
    )
    rows
  let distAt nu =
        case [d | (nu', d, _) <- rows, abs (nu' - nu) < 1e-12] of
          (d : _) -> d
          [] -> 1 / 0
      dNu0 = distAt 0.0
      dNu6 = distAt 0.6
  assertTrue "ν=0 minDist finite" (dNu0 < 1e6)
  assertTrue "faster evader not easier (ν=0.6 ≥ ν=0 minDist)" (dNu6 + 1e-6 >= dNu0)
  assertTrue "ν=0 captures in sweep horizon" (any (\(nu, _, c) -> abs nu < 1e-12 && c) rows)

  putStrLn "=== dubins-chase deck 0+1+1b+2 done ==="
