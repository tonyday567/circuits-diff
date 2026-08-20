{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StrictData #-}

-- | Dubins chase — pursuit–evasion as a circuits-diff consumer
-- (classically: /homicidal chauffeur/).
--
-- = Players
--
-- * __Pursuer__ — Dubins car: fixed speed 'pSpeed', min turn radius 'pTurnR'.
--   Control \(u \in [-1,1]\) selects signed curvature \(u / R\).
-- * __Evader__ — simple motion: fixed speed 'eSpeed', free heading \(\phi\).
--
-- = Decks
--
-- * __0__ — pure Euler steps + absolute rollout; kinematic sanity oracles.
-- * __1__ — soft-capture loss through the rollout; finite-difference gradients
--   w.r.t. pursuer controls (evader open-loop fixed).
-- * __1b__ — same dynamics\/loss written once polymorphic in a 'Lit' carrier;
--   reverse-mode gradients via 'Diff' (and 'DiffP' via 'toParam'); match FD.
-- * __2__ — open-loop optimizers (projected GD + backtracking) and hard-capture
--   scoring; public param sweeps.
--
-- Classical name retained only as literature keyword; working name is the
-- dynamics: /dubins-chase/.
module Circuit.Diff.DubinsChase
  ( -- * Parameters
    Params (..),
    defaultParams,

    -- * State
    Pose2,
    Pos2,
    World,

    -- * Steps
    clampU,
    dubinsStep,
    simpleStep,
    stepWorld,

    -- * Geometry
    distance,
    captured,

    -- * Rollout
    rollout,
    pursuerPath,
    evaderPath,

    -- * Soft capture + FD gradients (deck 1)
    softGap,
    softLossWorld,
    softLossPath,
    lossOfControls,
    gradU_FD_with,
    gradU_FD,
    descendU,

    -- * Polymorphic carrier + reverse mode (deck 1b)
    Lit (..),
    SoftRelu (..),
    TagDubins,
    Pose2A,
    Pos2A,
    WorldA,
    dubinsStepA,
    simpleStepA,
    stepWorldA,
    rolloutA,
    distanceA,
    softGapA,
    softLossWorldA,
    softLossPathA,
    lossOfControlsA,
    lossAsDiff,
    gradU_Diff,
    gradU_DiffP,
    lossDiffP,

    -- * Open-loop optimizers + hard scoring (deck 2)
    OptConfig (..),
    defaultOpt,
    lossTerminal,
    lossMinSoft,
    minDistancePath,
    everCaptured,
    captureTime,
    purePursuitU,
    optimizeU,
    sweepSpeedRatio,
  )
where

import Circuit.Diff (Diff (..), runDiff)
import Circuit.Diff.Carrier (Lit (..))
import Circuit.Diff.Param (DiffP (..), toParam)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Field qualified as NHF
import NumHask.Algebra.Multiplicative qualified as NHM
import Prelude

-- | Game parameters (SI-ish units; scale free for toy oracles).
data Params = Params
  { -- | Pursuer speed \(v_p > 0\).
    pSpeed :: Double,
    -- | Evader speed \(v_e \ge 0\) (usually \(v_e < v_p\)).
    eSpeed :: Double,
    -- | Pursuer minimum turn radius \(R > 0\).
    pTurnR :: Double,
    -- | Capture radius \(\ell \ge 0\).
    captureR :: Double
  }
  deriving (Eq, Show)

-- | Default toy: pursuer twice as fast as evader, unit turn radius, capture 0.1.
defaultParams :: Params
defaultParams =
  Params
    { pSpeed = 1.0,
      eSpeed = 0.5,
      pTurnR = 1.0,
      captureR = 0.1
    }

-- | Pursuer pose: \((x, y, \theta)\) with \(\theta\) heading (radians, CCW from +x).
type Pose2 = (Double, Double, Double)

-- | Planar position.
type Pos2 = (Double, Double)

-- | Absolute world: pursuer pose + evader position.
type World = (Pose2, Pos2)

-- | Clamp pursuer control to \([-1,1]\).
clampU :: Double -> Double
clampU u = max (-1) (min 1 u)

----------------------------------------------------------------------
-- Deck 1b — polymorphic carrier (Daisyworld lesson)
----------------------------------------------------------------------

-- | Rectified linear for soft capture.  Smooth almost everywhere; kink only
-- on the capture boundary (same as the Double 'max' in deck 1).
class SoftRelu a where
  softRelu :: a -> a

instance SoftRelu Double where
  softRelu = max 0

-- | Reverse-mode ReLU: forward uses the primal value; pullback is the
-- indicator of the positive half-line.
instance SoftRelu (Diff p Double Double) where
  softRelu (Diff f) = Diff $ \s ->
    let (y, pb) = f s
     in if y > 0
          then (y, pb)
          else (0, const 0)

-- | Phantom tag for reverse-mode probes of Dubins chase.
data TagDubins

type Pose2A a = (a, a, a)

type Pos2A a = (a, a)

type WorldA a = (Pose2A a, Pos2A a)

-- | Field bundle for the polymorphic dynamics.
type DynField a =
  ( Lit a,
    SoftRelu a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a,
    NHM.Divisive a,
    NHF.ExpField a,
    NHF.TrigField a
  )

-- | Polymorphic Dubins Euler step (no control clamp — project at the API edge).
dubinsStepA :: (DynField a) => Params -> a -> a -> Pose2A a -> Pose2A a
dubinsStepA p dt u (x, y, th) =
  let v = lit (pSpeed p)
      r = lit (pTurnR p)
      w = v NHM.* u NHM./ r
      th' = th NHA.+ w NHM.* dt
      x' = x NHA.+ v NHM.* NHF.cos th NHM.* dt
      y' = y NHA.+ v NHM.* NHF.sin th NHM.* dt
   in (x', y', th')

-- | Polymorphic simple-motion Euler step.
simpleStepA :: (DynField a) => Params -> a -> a -> Pos2A a -> Pos2A a
simpleStepA p dt phi (x, y) =
  let v = lit (eSpeed p)
   in (x NHA.+ v NHM.* NHF.cos phi NHM.* dt, y NHA.+ v NHM.* NHF.sin phi NHM.* dt)

-- | Polymorphic joint step.
stepWorldA :: (DynField a) => Params -> a -> a -> a -> WorldA a -> WorldA a
stepWorldA p dt u phi (pr, ev) =
  (dubinsStepA p dt u pr, simpleStepA p dt phi ev)

-- | Polymorphic absolute rollout.
rolloutA :: (DynField a) => Params -> a -> [(a, a)] -> WorldA a -> [WorldA a]
rolloutA p dt controls w0 = scanl step w0 controls
  where
    step w (u, phi) = stepWorldA p dt u phi w

-- | Polymorphic Euclidean distance.
distanceA :: (DynField a) => Pos2A a -> Pos2A a -> a
distanceA (x0, y0) (x1, y1) =
  let dx = x1 NHA.- x0
      dy = y1 NHA.- y0
   in NHF.sqrt (dx NHM.* dx NHA.+ dy NHM.* dy)

-- | Polymorphic soft gap \(d - \ell\).
softGapA :: (DynField a) => Params -> Pos2A a -> Pos2A a -> a
softGapA p a b = distanceA a b NHA.- lit (captureR p)

-- | Polymorphic soft loss: \(\tfrac12 \mathrm{softRelu}(d-\ell)^2\).
softLossWorldA :: (DynField a) => Params -> WorldA a -> a
softLossWorldA p ((xp, yp, _), e) =
  let g = softGapA p (xp, yp) e
      g' = softRelu g
   in lit 0.5 NHM.* g' NHM.* g'

-- | Polymorphic path-mean soft loss.
softLossPathA :: (DynField a) => Params -> [WorldA a] -> a
softLossPathA p ws =
  let n = lit (fromIntegral (length ws) :: Double)
   in if null ws
        then lit 0
        else foldr ((NHA.+) . softLossWorldA p) (lit 0) ws NHM./ n

-- | Polymorphic loss of pursuer controls vs fixed open-loop evader.
lossOfControlsA ::
  (DynField a) =>
  Params ->
  a ->
  [a] ->
  [a] ->
  WorldA a ->
  a
lossOfControlsA p dt us phis w0 =
  softLossPathA p (rolloutA p dt (zip us phis) w0)

-- | Inject a Double world into the active carrier.
litWorld :: (Lit a) => World -> WorldA a
litWorld ((x, y, th), (ex, ey)) =
  ((lit x, lit y, lit th), (lit ex, lit ey))

----------------------------------------------------------------------
-- Deck 0 / 1 Double specialisations (same physics as polymorphic core)
----------------------------------------------------------------------

-- | One Euler step of a Dubins car (control clamped to \([-1,1]\)).
dubinsStep :: Params -> Double -> Double -> Pose2 -> Pose2
dubinsStep p dt u = dubinsStepA p dt (clampU u)

-- | One Euler step of simple motion at heading \(\phi\).
simpleStep :: Params -> Double -> Double -> Pos2 -> Pos2
simpleStep = simpleStepA

-- | Joint absolute step.
stepWorld :: Params -> Double -> Double -> Double -> World -> World
stepWorld p dt u phi = stepWorldA p dt (clampU u) phi

-- | Euclidean distance between positions.
distance :: Pos2 -> Pos2 -> Double
distance = distanceA

-- | Hard capture: distance \(\le \ell\).
captured :: Params -> Pos2 -> Pos2 -> Bool
captured p a b = distance a b <= captureR p

-- | Absolute rollout from initial world.
rollout :: Params -> Double -> [(Double, Double)] -> World -> [World]
rollout p dt controls w0 =
  rolloutA p dt [(clampU u, phi) | (u, phi) <- controls] w0

-- | Pursuer \((x,y)\) samples along a rollout.
pursuerPath :: [World] -> [Pos2]
pursuerPath = map (\((x, y, _), _) -> (x, y))

-- | Evader samples along a rollout.
evaderPath :: [World] -> [Pos2]
evaderPath = map snd

----------------------------------------------------------------------
-- Deck 1 — soft capture + FD through rollout
----------------------------------------------------------------------

-- | Soft gap: \(d - \ell\) (positive = still outside capture).
softGap :: Params -> Pos2 -> Pos2 -> Double
softGap = softGapA

-- | Smooth loss on one world state: \(\tfrac12 \max(0, d-\ell)^2\).
softLossWorld :: Params -> World -> Double
softLossWorld = softLossWorldA

-- | Path loss: mean soft loss over the rollout (including the initial state).
softLossPath :: Params -> [World] -> Double
softLossPath = softLossPathA

-- | Loss of a pursuer control sequence against a fixed open-loop evader.
lossOfControls :: Params -> Double -> [Double] -> [Double] -> World -> Double
lossOfControls p dt us phis w0 =
  lossOfControlsA p dt (map clampU us) phis (litWorld w0)

-- | Central finite-difference gradient of a scalar loss w.r.t. each \(u_t\).
gradU_FD_with ::
  (Params -> Double -> [Double] -> [Double] -> World -> Double) ->
  Params ->
  Double ->
  Double ->
  [Double] ->
  [Double] ->
  World ->
  [Double]
gradU_FD_with lossFn p dt eps us phis w0 =
  [ (lossFn p dt (bump i eps) phis w0 - lossFn p dt (bump i (-eps)) phis w0)
      / (2 * eps)
  | i <- [0 .. length us - 1]
  ]
  where
    bump i e =
      [ if j == i then clampU (u + e) else u
      | (j, u) <- zip [0 ..] us
      ]

-- | FD gradient of path-mean soft loss ('lossOfControls').
gradU_FD :: Params -> Double -> Double -> [Double] -> [Double] -> World -> [Double]
gradU_FD = gradU_FD_with lossOfControls

-- | One projected gradient step on pursuer controls (evader fixed).
descendU :: Params -> Double -> Double -> Double -> [Double] -> [Double] -> World -> [Double]
descendU p dt eps eta us phis w0 =
  let g = gradU_FD p dt eps us phis w0
   in zipWith (\u gi -> clampU (u - eta * gi)) us g

----------------------------------------------------------------------
-- Deck 1b — reverse-mode gradients (Diff + DiffP)
----------------------------------------------------------------------

-- | Path-mean soft loss as a 'Diff' in one pursuer control \(u_i\).
--
-- Control \(u_i\) is the independent variable ('Diff @(,id)@); all other
-- controls, headings, time step, and the initial world are 'lit' constants.
-- Same polymorphic RHS as simulation — Daisyworld lesson.
lossAsDiff ::
  Params ->
  Double ->
  Int ->
  [Double] ->
  [Double] ->
  World ->
  Diff TagDubins Double Double
lossAsDiff p dt i us phis w0 =
  let usD =
        [ if j == i
            then Diff (,id)
            else lit (clampU u)
        | (j, u) <- zip [0 ..] us
        ]
      phisD = map lit phis
      dtD = lit dt
      w0D = litWorld w0
   in lossOfControlsA p dtD usD phisD w0D

-- | Reverse-mode gradient of 'lossOfControls' w.r.t. each \(u_t\).
--
-- One reverse pass per control (Daisyworld column style).  Oracle: match
-- 'gradU_FD' on open-interval controls (no clamp kink).
gradU_Diff :: Params -> Double -> [Double] -> [Double] -> World -> [Double]
gradU_Diff p dt us phis w0 =
  [ let (_, pb) = runDiff (lossAsDiff p dt i us phis w0) (clampU (us !! i))
     in pb 1
  | i <- [0 .. length us - 1]
  ]

-- | Same single-control loss as 'DiffP ()' via 'toParam'.
--
-- Shows the DiffP carrier on the identical 'Diff' computation — not a second
-- hand-written physics.
lossDiffP ::
  Params ->
  Double ->
  Int ->
  [Double] ->
  [Double] ->
  World ->
  DiffP () Double Double
lossDiffP p dt i us phis w0 =
  toParam (lossAsDiff p dt i us phis w0)

-- | Reverse-mode gradient via 'DiffP' ('toParam' of 'lossAsDiff).
--
-- Must match 'gradU_Diff (same pullback, different wrapper).
gradU_DiffP :: Params -> Double -> [Double] -> [Double] -> World -> [Double]
gradU_DiffP p dt us phis w0 =
  [ let (_, pb) = runDiffP (lossDiffP p dt i us phis w0) () (clampU (us !! i))
        (du, ()) = pb 1
     in du
  | i <- [0 .. length us - 1]
  ]

----------------------------------------------------------------------
-- Deck 2 — open-loop optimizers + hard scoring
----------------------------------------------------------------------

-- | Optimizer knobs for projected gradient on open-loop \(u_t\).
data OptConfig = OptConfig
  { -- | Integration step (same as rollout).
    ocDt :: Double,
    -- | Central-FD epsilon (fallback / FD oracles).
    ocEps :: Double,
    -- | Initial trial step size along \(-\nabla u\).
    ocEta0 :: Double,
    -- | Maximum projected-GD iterations.
    ocMaxIters :: Int,
    -- | Backtracking factor \(\beta \in (0,1)\).
    ocBeta :: Double,
    -- | Stop when relative loss drop falls below this.
    ocTol :: Double
  }
  deriving (Eq, Show)

-- | Defaults tuned for the deck-2 toy oracles (not for production MPC).
defaultOpt :: OptConfig
defaultOpt =
  OptConfig
    { ocDt = 0.05,
      ocEps = 1e-4,
      ocEta0 = 2.0,
      ocMaxIters = 40,
      ocBeta = 0.5,
      ocTol = 1e-8
    }

-- | Terminal soft loss (final state only).
lossTerminal :: Params -> Double -> [Double] -> [Double] -> World -> Double
lossTerminal p dt us phis w0 =
  let path = rollout p dt (zip us phis) w0
   in case reverse path of
        (w : _) -> softLossWorld p w
        [] -> 0

-- | Minimum soft loss along the path — aligns with hard min-distance /
-- capture scoring (zero iff some sample is inside the capture disk).
lossMinSoft :: Params -> Double -> [Double] -> [Double] -> World -> Double
lossMinSoft p dt us phis w0 =
  let path = rollout p dt (zip us phis) w0
   in case map (softLossWorld p) path of
        [] -> 0
        xs -> minimum xs

-- | Minimum pursuer–evader distance along a path (hard geometry).
minDistancePath :: [World] -> Double
minDistancePath [] = 1 / 0 -- +∞
minDistancePath ws =
  minimum
    [ distance (xp, yp) e
    | ((xp, yp, _), e) <- ws
    ]

-- | Whether hard capture occurred on any sample of the path.
everCaptured :: Params -> [World] -> Bool
everCaptured p =
  any
    (\((xp, yp, _), e) -> captured p (xp, yp) e)

-- | First time (step index × dt) at which hard capture holds; 'Nothing' if never.
captureTime :: Params -> Double -> [World] -> Maybe Double
captureTime p dt ws =
  case [i | (i, ((xp, yp, _), e)) <- zip [(0 :: Int) ..] ws, captured p (xp, yp) e] of
    (i : _) -> Just (fromIntegral i * dt)
    [] -> Nothing

-- | Open-loop pure-pursuit heuristic against fixed headings @phis@.
purePursuitU :: Params -> Double -> [Double] -> World -> [Double]
purePursuitU p dt phis w0 =
  go w0 phis
  where
    go _ [] = []
    go w (phi : rest) =
      let ((px, py, th), (ex, ey)) = w
          (ex', ey') = simpleStep p dt phi (ex, ey)
          want = atan2 (ey' - py) (ex' - px)
          err0 = atan2 (sin (want - th)) (cos (want - th))
          err =
            if abs err0 > pi - 1e-6
              then pi - 1e-6
              else err0
          u = clampU (2 * err)
       in u : go (stepWorld p dt u phi w) rest

-- | Multi-step projected gradient descent on pursuer controls.
--
-- Minimizes 'lossMinSoft' with Armijo backtracking.  Gradients from reverse
-- mode on path-mean soft loss when the min is smooth enough for progress;
-- uses 'gradU_FD_with' 'lossMinSoft' so the objective and gradient agree
-- (min-along-path is non-smooth; FD subgradient is the honest oracle).
optimizeU ::
  Params ->
  OptConfig ->
  [Double] ->
  [Double] ->
  World ->
  ([Double], [Double])
optimizeU p cfg us0 phis w0 =
  let l0 = lossOf us0
   in go (ocMaxIters cfg) us0 [l0]
  where
    dt = ocDt cfg
    eps = ocEps cfg
    lossOf us = lossMinSoft p dt us phis w0
    go 0 us hist = (us, reverse hist)
    go k us hist@(lPrev : _) =
      let g = gradU_FD_with lossMinSoft p dt eps us phis w0
          gNorm = sqrt (sum (map (\gi -> gi * gi) g))
       in if gNorm < 1e-12
            then (us, reverse hist)
            else case backtrack (ocEta0 cfg) us g lPrev of
              Nothing -> (us, reverse hist)
              Just (us', l') ->
                if abs (lPrev - l') < ocTol cfg * (1 + abs lPrev)
                  then (us', reverse (l' : hist))
                  else go (k - 1) us' (l' : hist)
    go _ us hist = (us, reverse hist)

    backtrack eta us g lPrev
      | eta < 1e-12 = Nothing
      | otherwise =
          let us' = zipWith (\u gi -> clampU (u - eta * gi)) us g
              l' = lossOf us'
           in if l' < lPrev - 1e-14
                then Just (us', l')
                else backtrack (ocBeta cfg * eta) us g lPrev

-- | Public param sweep: for each speed ratio \(\nu = v_e / v_p\), optimize
-- open-loop \(u\) against a fixed-heading flee and report min distance.
sweepSpeedRatio ::
  Params ->
  OptConfig ->
  [Double] ->
  [Double] ->
  World ->
  [Double] ->
  [(Double, Double, Bool)]
sweepSpeedRatio base cfg nus phis w0 us0 =
  [ let p = base {eSpeed = nu * pSpeed base}
        (usOpt, _) = optimizeU p cfg us0 phis w0
        path = rollout p (ocDt cfg) (zip usOpt phis) w0
     in (nu, minDistancePath path, everCaptured p path)
  | nu <- nus
  ]
