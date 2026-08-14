{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Homeostasis is a pullback number.
--
-- = The idea
--
-- Watson and Lovelock's /Daisyworld/ (Tellus 1983) is a toy climate in which
-- black and white daisies regulate planetary temperature as solar luminosity
-- varies.  The iconic picture is a __plateau__: effective temperature \(T^*\)
-- stays nearly flat across a wide band of luminosity \(L\), while a bare
-- planet (no life) warms steeply.
--
-- That plateau is a derivative claim: \(\mathrm{d}T^*/\mathrm{d}L \approx 0\).
-- And \(T^*\) is not a free parameter — it is the temperature of an
-- __equilibrium__ of the daisy ODEs.  Sensitivity of a fixpoint to a parameter
-- is the classical implicit-function theorem:
--
-- \[
--   \frac{\mathrm{d}\alpha^*}{\mathrm{d}L}
--     = -\Bigl(\frac{\partial f}{\partial\alpha}\Bigr)^{-1}
--        \frac{\partial f}{\partial L},
--   \qquad
--   \frac{\mathrm{d}T^*}{\mathrm{d}L}
--     = \frac{\partial T}{\partial\alpha}\cdot
--       \frac{\mathrm{d}\alpha^*}{\mathrm{d}L}
--       + \frac{\partial T}{\partial L}.
-- \]
--
-- In this library those Jacobians are not hand-coded.  They are the pullbacks
-- of a single polymorphic right-hand side, instantiated at a tagged 'Diff''
-- carrier.  The same expression that /simulates/ Daisyworld /measures/
-- homeostasis.
--
-- = One right-hand side
--
-- Write the ODE once, polymorphic in a NumHask field carrier.  Constants
-- enter through 'Lit'.  Instantiating at 'Double' gives forward simulation;
-- instantiating at @'Diff'' p 'Double' 'Double'@ gives reverse-mode derivatives
-- of every intermediate — no second, hand-synchronised copy of the physics.
--
-- = What you get
--
-- * 'daisyRHS' — the ODE \(\dot\alpha = f(\alpha; L)\).
-- * 'newtonEq' — a Newton solve for \(f(\alpha^*; L) = 0\).
-- * 'dTstar_dL' — \(\mathrm{d}T^*/\mathrm{d}L\) by the IFT formula above,
--   with every partial from the tagged-'Diff'' tower.
-- * 'bareTe' — the no-life control, same Stefan–Boltzmann physics.
--
-- The regulation ratio \(\lvert\mathrm{d}T^*/\mathrm{d}L\rvert /
-- \lvert\mathrm{d}T_{\mathrm{bare}}/\mathrm{d}L\rvert\) is then a ratio of
-- two pullback numbers.  That is the pearl: homeostasis, computed.
module Circuit.Diff.Daisyworld
  ( -- * Carrier injection
    Lit (..),

    -- * Parameters (Watson–Lovelock 1983 toy)
    aBlack,
    aWhite,
    aGround,
    solarS,
    sigmaSB,
    qInsul,
    gammaDeath,
    tOpt,
    kGrowth,

    -- * The single polymorphic model
    planetaryAlbedo,
    effectiveTemp,
    localTemp,
    betaRaw,
    daisyRHS,
    planetTe,
    bareTe,

    -- * Double specialisations (simulation)
    rhsD,
    teD,
    bareTeD,

    -- * Equilibrium
    newtonEq,
    projectSimplex,

    -- * Homeostasis as a pullback
    dTstar_dL,
    dTstar_dL_FD,
    dBare_dL,
  )
where

import Circuit.Diff.Circuit (Diff', runDiff, pattern Diff)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Field qualified as NHF
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Prelude
import Prelude ()

-- $setup
-- >>> import Circuit.Diff.Daisyworld
-- >>> import Prelude (abs, (>) )

-- ---------------------------------------------------------------------------
-- Carrier injection
-- ---------------------------------------------------------------------------

-- | Lift a numeric literal into the active carrier.
--
-- @
-- instance Lit Double where lit = id
-- instance Lit (Diff' p Double Double) where lit c = constant c
-- @
--
-- Every coefficient in the model — albedos, Stefan–Boltzmann, death rate —
-- is written @'lit' c@ once, and resolves correctly under both simulation
-- and differentiation.
class Lit a where
  lit :: Double -> a

instance Lit Double where
  lit = id

instance Lit (Diff' p Double Double) where
  lit c = Diff (const (c, const 0))

-- Phantom tag for reverse-mode probes of the Daisyworld RHS.
data TagDaisy

-- ---------------------------------------------------------------------------
-- Parameters
-- ---------------------------------------------------------------------------

-- | Black-daisy albedo.
aBlack :: Double
aBlack = 0.25

-- | White-daisy albedo.
aWhite :: Double
aWhite = 0.75

-- | Bare-ground albedo.
aGround :: Double
aGround = 0.50

-- | Solar constant (W\/m²), Watson–Lovelock scale.
solarS :: Double
solarS = 917

-- | Stefan–Boltzmann constant.
sigmaSB :: Double
sigmaSB = 5.67e-8

-- | Insulation parameter relating local and planetary temperature (K).
qInsul :: Double
qInsul = 20

-- | Daisy death rate.
gammaDeath :: Double
gammaDeath = 0.3

-- | Optimal growth temperature (K).
tOpt :: Double
tOpt = 295.5

-- | Growth parabola coefficient: \(\beta = 0\) at \(T_{\mathrm{opt}}\pm 17.5\).
kGrowth :: Double
kGrowth = 1 / (17.5 * 17.5)

-- ---------------------------------------------------------------------------
-- The model — written once
-- ---------------------------------------------------------------------------

-- | Planetary albedo \(A = \alpha_b A_b + \alpha_w A_w + x A_g\),
-- with bare fraction \(x = 1 - \alpha_b - \alpha_w\).
planetaryAlbedo ::
  (Lit a, NHA.Additive a, NHA.Subtractive a, NHM.Multiplicative a) =>
  a ->
  a ->
  a
planetaryAlbedo ab aw =
  let x = lit 1 NHA.- ab NHA.- aw
   in ab NHM.* lit aBlack
        NHA.+ aw NHM.* lit aWhite
        NHA.+ x NHM.* lit aGround

-- | Effective temperature from Stefan–Boltzmann:
-- \(\sigma T_e^4 = S\cdot L\cdot(1-A)\).
effectiveTemp ::
  ( Lit a,
    NHF.ExpField a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a,
    NHM.Divisive a
  ) =>
  a -> -- L
  a -> -- A
  a
effectiveTemp l a =
  let flux = lit solarS NHM.* l NHM.* (lit 1 NHA.- a)
   in NHF.sqrt (NHF.sqrt (flux NHM./ lit sigmaSB))

-- | Local temperature of a daisy type: \(T_i = q(A - A_i) + T_e\).
localTemp ::
  (Lit a, NHA.Additive a, NHA.Subtractive a, NHM.Multiplicative a) =>
  a -> -- planetary A
  a -> -- type albedo A_i
  a -> -- T_e
  a
localTemp a ai te = lit qInsul NHM.* (a NHA.- ai) NHA.+ te

-- | Growth parabola \(\beta(T) = 1 - k(T_{\mathrm{opt}} - T)^2\)
-- (unclamped; at interior equilibria \(\beta > 0\)).
betaRaw ::
  (Lit a, NHA.Additive a, NHA.Subtractive a, NHM.Multiplicative a) =>
  a ->
  a
betaRaw t =
  let d = lit tOpt NHA.- t
   in lit 1 NHA.- lit kGrowth NHM.* d NHM.* d

-- | The Daisyworld ODE — __the single polymorphic right-hand side__.
--
-- State is \([\alpha_b, \alpha_w]\).  Dynamics:
--
-- \[
--   \dot\alpha_i = \alpha_i\bigl(x\cdot\beta(T_i) - \gamma\bigr).
-- \]
--
-- Instantiate at 'Double' to step or Newton-solve.  Instantiate at
-- @'Diff'' p 'Double' 'Double'@ (via 'Lit') to obtain \(\partial f/\partial\alpha\)
-- and \(\partial f/\partial L\) by reverse mode — the Jacobians the IFT needs.
daisyRHS ::
  ( Lit a,
    NHF.ExpField a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a,
    NHM.Divisive a
  ) =>
  a -> -- luminosity L
  [a] -> -- [α_b, α_w]
  [a] -- [α̇_b, α̇_w]
daisyRHS l [ab, aw] =
  let x = lit 1 NHA.- ab NHA.- aw
      a = planetaryAlbedo ab aw
      te = effectiveTemp l a
      tb = localTemp a (lit aBlack) te
      tw = localTemp a (lit aWhite) te
      fab = ab NHM.* (x NHM.* betaRaw tb NHA.- lit gammaDeath)
      faw = aw NHM.* (x NHM.* betaRaw tw NHA.- lit gammaDeath)
   in [fab, faw]
daisyRHS _ _ = error "daisyRHS: expected [α_b, α_w]"

-- | Planetary effective temperature from state and luminosity.
planetTe ::
  ( Lit a,
    NHF.ExpField a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a,
    NHM.Divisive a
  ) =>
  a ->
  [a] ->
  a
planetTe l [ab, aw] = effectiveTemp l (planetaryAlbedo ab aw)
planetTe _ _ = error "planetTe: expected [α_b, α_w]"

-- | Bare-planet temperature (no daisies): same Stefan–Boltzmann law at
-- ground albedo.  The control against which regulation is measured.
bareTe ::
  ( Lit a,
    NHF.ExpField a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a,
    NHM.Divisive a
  ) =>
  a ->
  a
bareTe l = effectiveTemp l (lit aGround)

-- ---------------------------------------------------------------------------
-- Double view — simulation
-- ---------------------------------------------------------------------------

-- | @daisyRHS@ at 'Double'.
rhsD :: Double -> [Double] -> [Double]
rhsD = daisyRHS

-- | @planetTe@ at 'Double'.
teD :: Double -> [Double] -> Double
teD = planetTe

-- | @bareTe@ at 'Double'.
bareTeD :: Double -> Double
bareTeD = bareTe

-- ---------------------------------------------------------------------------
-- Tagged-Diff Jacobians — still the same RHS
-- ---------------------------------------------------------------------------

-- | \(\partial f/\partial\alpha\) at a Double point, columns via reverse mode.
jacobianAlpha :: Double -> [Double] -> [[Double]]
jacobianAlpha l s0 =
  let col k =
        let sk = Diff (,id) :: Diff' TagDaisy Double Double
            s =
              [ if i == k then sk else lit (s0 !! i)
              | i <- [0, 1]
              ]
            outs = daisyRHS (lit l :: Diff' TagDaisy Double Double) s
         in [let (_, pb) = runDiff (outs !! i) (s0 !! k) in pb 1 | i <- [0, 1]]
   in let cols = [col 0, col 1]
       in [[(cols !! j) !! i | j <- [0, 1]] | i <- [0, 1]]

-- | \(\partial f/\partial L\) at fixed \(\alpha\).
dfdL :: Double -> [Double] -> [Double]
dfdL l0 s0 =
  let lVar = Diff (,id) :: Diff' TagDaisy Double Double
      sC = [lit (s0 !! i) :: Diff' TagDaisy Double Double | i <- [0, 1]]
      outs = daisyRHS lVar sC
   in [let (_, pb) = runDiff (outs !! i) l0 in pb 1 | i <- [0, 1]]

-- | \((\partial T/\partial\alpha_b,\; \partial T/\partial\alpha_w,\; \partial T/\partial L)\).
dTeParts :: Double -> [Double] -> (Double, Double, Double)
dTeParts l0 s0 =
  let abV = Diff (,id) :: Diff' TagDaisy Double Double
      (_, pAb) = runDiff (planetTe (lit l0) [abV, lit (s0 !! 1)]) (s0 !! 0)
      awV = Diff (,id) :: Diff' TagDaisy Double Double
      (_, pAw) = runDiff (planetTe (lit l0) [lit (s0 !! 0), awV]) (s0 !! 1)
      lV = Diff (,id) :: Diff' TagDaisy Double Double
      sC = [lit (s0 !! i) :: Diff' TagDaisy Double Double | i <- [0, 1]]
      (_, pL) = runDiff (planetTe lV sC) l0
   in (pAb 1, pAw 1, pL 1)

-- ---------------------------------------------------------------------------
-- Linear algebra (2×2) and Newton
-- ---------------------------------------------------------------------------

solve2 :: [[Double]] -> [Double] -> [Double]
solve2 [[a, b], [c, d]] [r, s] =
  let det = a * d - b * c
   in if abs det < 1e-14
        then [0, 0]
        else [(d * r - b * s) / det, (a * s - c * r) / det]
solve2 _ _ = error "solve2: expected 2×2"

-- | Project onto the probability simplex \(\alpha_b,\alpha_w \ge 0\),
-- \(\alpha_b+\alpha_w \le 0.99\).
projectSimplex :: [Double] -> [Double]
projectSimplex [ab, aw] =
  let ab' = max 0 ab
      aw' = max 0 aw
      s = ab' + aw'
   in if s > 0.99 then [ab' * 0.99 / s, aw' * 0.99 / s] else [ab', aw']
projectSimplex s = s

-- | Newton solve for \(f(\alpha^*; L) = 0\), Jacobian from 'jacobianAlpha'.
--
-- Damped steps + simplex projection after every update keep
-- \(\alpha_b,\alpha_w \in [0,1]\) with \(\alpha_b+\alpha_w \le 0.99\).  When both
-- daisy types are present at equilibrium the Watson–Lovelock identity
-- \(x\cdot\beta_b = x\cdot\beta_w = \gamma\) forces a constant total coverage
-- \(\alpha_b+\alpha_w \approx 0.673\) under the standard parameters (see the
-- oracle harness).
--
-- >>> let s = newtonEq 1.0 [0.3, 0.3]
-- >>> let res = sqrt (sum (map (\x -> x*x) (rhsD 1.0 s)))
-- >>> res < 1e-10
-- True
-- >>> let [ab,aw] = s
-- >>> ab >= 0 && aw >= 0 && ab + aw <= 1
-- True
newtonEq :: Double -> [Double] -> [Double]
newtonEq l s0 =
  let go 0 s = projectSimplex s
      go n s =
        let f = rhsD l s
            j = jacobianAlpha l s
            raw = solve2 j (map negate f)
            -- damped Newton
            delta = map (0.5 *) raw
            s' = projectSimplex (zipWith (+) s delta)
         in if sqrt (sum (map (\x -> x * x) f)) < 1e-12
              then projectSimplex s
              else go (n - 1 :: Int) s'
   in go 80 (projectSimplex s0)

-- ---------------------------------------------------------------------------
-- Homeostasis = pullback number
-- ---------------------------------------------------------------------------

-- | \(\mathrm{d}T^*/\mathrm{d}L\) at an equilibrium, by the IFT.
--
-- Every partial is a reverse-mode pullback of 'daisyRHS' \/ 'planetTe' —
-- still the single polymorphic model.
--
-- >>> let s = newtonEq 1.0 [0.3, 0.3]
-- >>> let d = dTstar_dL 1.0 s
-- >>> let bare = dBare_dL 1.0
-- >>> abs d < 0.3 * abs bare   -- regulated ≪ bare
-- True
dTstar_dL :: Double -> [Double] -> Double
dTstar_dL l sStar =
  let j = jacobianAlpha l sStar
      dAlpha = solve2 j (map negate (dfdL l sStar))
      (dtAb, dtAw, dtL) = dTeParts l sStar
      dab = case dAlpha of
        (x : _) -> x
        _ -> 0
      daw = case dAlpha of
        (_ : y : _) -> y
        _ -> 0
   in dtAb * dab + dtAw * daw + dtL

-- | Finite-difference check of 'dTstar_dL' (continuation from @sStar@).
dTstar_dL_FD :: Double -> Double -> [Double] -> Double
dTstar_dL_FD l eps sStar =
  let sPlus = newtonEq (l + eps) sStar
      sMinus = newtonEq (l - eps) sStar
   in (teD (l + eps) sPlus - teD (l - eps) sMinus) / (2 * eps)

-- | \(\mathrm{d}T_{\mathrm{bare}}/\mathrm{d}L\) by reverse mode on 'bareTe'.
dBare_dL :: Double -> Double
dBare_dL l0 =
  let (_, pb) = runDiff (bareTe (Diff (,id) :: Diff' TagDaisy Double Double)) l0
   in pb 1
