{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Riemann curvature from a Levi-Civita connection.
--
-- Following the classical identity (Albert arXiv:2312.02664 Def. 6)
--
-- > R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ}
--
-- built on 'christoffel2D' for 2-D coordinate metrics, plus a diagonal-metric
-- path for the 4-D Schwarzschild vacuum oracle.
module Circuit.Diff.Curvature
  ( -- * 2-D Riemann / Ricci
    Gamma2D,
    gamma2DAt,
    riemann2D,
    ricci2D,
    ricciScalar2D,

    -- * 2-D metrics
    sphereMetricLower,
    sphereMetricRaise,

    -- * Diagonal n-D (Schwarzschild)
    DiagonalMetric (..),
    schwarzschildMetric,
    gammaDiagonal,
    riemannDiagonal,
    ricciDiagonal,
  )
where

import Circuit.Diff (Diff, runDiff, pattern Diff)
import Circuit.Diff.Chart
  ( christoffel2D,
    raise2D,
  )
import NumHask.Prelude
import Prelude ()

-- | Packed Christoffel symbols @Γ^c_{ab}@ for a 2-D chart (c,a,b ∈ {0,1}).
type Gamma2D a = (a, a, a, a, a, a, a, a)

-- | @Γ^c_{ab}@ lookup.
gammaComp :: Gamma2D a -> Int -> Int -> Int -> a
gammaComp (g000, g001, g010, g011, g100, g101, g110, g111) c a b =
  case (c, a, b) of
    (0, 0, 0) -> g000
    (0, 0, 1) -> g001
    (0, 1, 0) -> g010
    (0, 1, 1) -> g011
    (1, 0, 0) -> g100
    (1, 0, 1) -> g101
    (1, 1, 0) -> g110
    (1, 1, 1) -> g111
    _ -> error "gammaComp: index out of range"

gamma2DAt ::
  (Field a) =>
  Diff ((a, a), (a, a)) (a, a) ->
  Diff ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  Gamma2D a
gamma2DAt = christoffel2D

-- | Central difference step for ∂Γ.
fdStep :: (Field a, FromInteger a) => a
fdStep = one / fromInteger (10000000 :: Integer)

-- | Basis step along coordinate @i@.
bump2 :: (Additive a) => Int -> a -> (a, a) -> (a, a)
bump2 0 h (x0, x1) = (x0 + h, x1)
bump2 1 h (x0, x1) = (x0, x1 + h)
bump2 _ _ _ = error "bump2: bad index"

-- | @∂_μ Γ^ρ_{ab}@ by central differences of 'christoffel2D'.
partialGamma2D ::
  (Field a, FromInteger a) =>
  Diff ((a, a), (a, a)) (a, a) ->
  Diff ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  Int ->
  Int ->
  Int ->
  Int ->
  a
partialGamma2D lower raise x mu rho a b =
  let h = fdStep
      gPlus = gamma2DAt lower raise (bump2 mu h x)
      gMinus = gamma2DAt lower raise (bump2 mu (negate h) x)
      twoH = h + h
   in (gammaComp gPlus rho a b - gammaComp gMinus rho a b) / twoH

-- | Riemann component @R^ρ_{σμν}@ at a point (2-D).
--
-- > R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ}
-- >           + Γ^ρ_{μλ} Γ^λ_{νσ} − Γ^ρ_{νλ} Γ^λ_{μσ}
riemann2D ::
  (Field a, FromInteger a) =>
  Diff ((a, a), (a, a)) (a, a) ->
  Diff ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  Int ->
  Int ->
  Int ->
  Int ->
  a
riemann2D lower raise x rho sigma mu nu =
  let g = gamma2DAt lower raise x
      dMu = partialGamma2D lower raise x mu rho nu sigma
      dNu = partialGamma2D lower raise x nu rho mu sigma
      quad =
        sum
          [ gammaComp g rho mu lam
              * gammaComp g lam nu sigma
              - gammaComp g rho nu lam
              * gammaComp g lam mu sigma
          | lam <- [0, 1]
          ]
   in dMu - dNu + quad

-- | Ricci @R_{σν} = R^ρ_{σρν}@ (sum on ρ).
ricci2D ::
  (Field a, FromInteger a) =>
  Diff ((a, a), (a, a)) (a, a) ->
  Diff ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  Int ->
  Int ->
  a
ricci2D lower raise x sigma nu =
  sum [riemann2D lower raise x rho sigma rho nu | rho <- [0, 1]]

-- | Ricci scalar @R = g^{σν} R_{σν}@.
ricciScalar2D ::
  (Field a, FromInteger a) =>
  Diff ((a, a), (a, a)) (a, a) ->
  Diff ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  a
ricciScalar2D lower raise x =
  let (gInv0, _) = runDiff raise (x, (one, zero))
      (gInv1, _) = runDiff raise (x, (zero, one))
      g00 = fst gInv0
      g01 = fst gInv1
      g10 = snd gInv0
      g11 = snd gInv1
      r00 = ricci2D lower raise x 0 0
      r01 = ricci2D lower raise x 0 1
      r10 = ricci2D lower raise x 1 0
      r11 = ricci2D lower raise x 1 1
   in g00 * r00 + g01 * r01 + g10 * r10 + g11 * r11

--------------------------------------------------------------------------------
-- Unit sphere metric (θ, φ):  g = diag(1, sin²θ)
--------------------------------------------------------------------------------

-- | Unit 2-sphere metric in spherical coordinates @(θ, φ)@.
--
-- @ds² = dθ² + sin²θ dφ²@.  Analytic Ricci scalar is @2@.
sphereMetricLower :: (TrigField a) => Diff ((a, a), (a, a)) (a, a)
sphereMetricLower = Diff $ \((theta, _), (vth, vph)) ->
  let s = sin theta
      ss = s * s
      tw = one + one
   in ( (vth, ss * vph),
        \(dcth, dcph) ->
          ( (tw * s * cos theta * vph * dcph, zero),
            (dcth, ss * dcph)
          )
      )

sphereMetricRaise :: (TrigField a) => Diff ((a, a), (a, a)) (a, a)
sphereMetricRaise = raise2D sphereMetricLower

--------------------------------------------------------------------------------
-- Diagonal metrics (Schwarzschild)
--------------------------------------------------------------------------------

-- | A diagonal metric given by its diagonal components @g_ii(x)@ and their
-- first partials @∂_j g_ii(x)@ (no sum).
data DiagonalMetric a = DiagonalMetric
  { dmDim :: Int,
    dmG :: [a] -> Int -> a,
    dmDG :: [a] -> Int -> Int -> a
  }

-- | Schwarzschild metric outside the horizon (@r > 2M@).
--
-- Coordinates @(t, r, θ, φ)@; @rs = 2M@ is the Schwarzschild radius.
--
-- > g = diag( −(1−rs/r), 1/(1−rs/r), r², r² sin²θ )
schwarzschildMetric :: (TrigField a) => a -> DiagonalMetric a
schwarzschildMetric rs =
  DiagonalMetric
    { dmDim = 4,
      dmG = \xs i ->
        let r = xs !! 1
            th = xs !! 2
            f = one - rs / r
         in case i of
              0 -> negate f
              1 -> recip f
              2 -> r * r
              3 -> r * r * sin th * sin th
              _ -> error "schwarzschildMetric: bad index",
      dmDG = \xs j i ->
        let r = xs !! 1
            th = xs !! 2
            f = one - rs / r
            -- ∂_r f = rs/r²
            dFdr = rs / (r * r)
         in case (j, i) of
              -- only r-derivatives of g_tt, g_rr; θ-derivative of g_φφ
              (1, 0) -> negate dFdr
              (1, 1) -> negate dFdr / (f * f)
              (1, 2) -> (one + one) * r
              (1, 3) -> (one + one) * r * sin th * sin th
              (2, 3) -> (one + one) * r * r * sin th * cos th
              _ -> zero
    }

-- | Inverse diagonal: @g^{ii} = 1/g_ii@.
gInvDiag :: (Field a) => DiagonalMetric a -> [a] -> Int -> a
gInvDiag m x i = recip (dmG m x i)

-- | Christoffel @Γ^c_{ab}@ for a diagonal metric.
--
-- > Γ^c_{ab} = ½ g^{cc} (∂_a g_{bc} + ∂_b g_{ac} − ∂_c g_{ab})  (no sum on c)
gammaDiagonal :: (Field a) => DiagonalMetric a -> [a] -> Int -> Int -> Int -> a
gammaDiagonal m x c a b =
  let gInv = gInvDiag m x c
      -- g_ab is zero unless a==b for diagonal metrics
      dg a' b' c' =
        if a' == b'
          then dmDG m x c' a'
          else zero
      term = dg b c a + dg a c b - dg a b c
   in half * gInv * term

-- | @∂_μ Γ^c_{ab}@ by central differences on coordinate @μ@.
partialGammaDiagonal ::
  (Field a, FromInteger a) =>
  DiagonalMetric a ->
  [a] ->
  Int ->
  Int ->
  Int ->
  Int ->
  a
partialGammaDiagonal m x mu c a b =
  let h = fdStep
      n = dmDim m
      bump j =
        [ if k == mu then (x !! k) + j * h else x !! k
        | k <- [0 .. n - 1]
        ]
      twoH = h + h
   in ( gammaDiagonal m (bump one) c a b
          - gammaDiagonal m (bump (negate one)) c a b
      )
        / twoH

-- | Riemann @R^ρ_{σμν}@ for a diagonal metric.
riemannDiagonal ::
  (Field a, FromInteger a) =>
  DiagonalMetric a ->
  [a] ->
  Int ->
  Int ->
  Int ->
  Int ->
  a
riemannDiagonal m x rho sigma mu nu =
  let n = dmDim m
      dMu = partialGammaDiagonal m x mu rho nu sigma
      dNu = partialGammaDiagonal m x nu rho mu sigma
      quad =
        sum
          [ gammaDiagonal m x rho mu lam
              * gammaDiagonal m x lam nu sigma
              - gammaDiagonal m x rho nu lam
              * gammaDiagonal m x lam mu sigma
          | lam <- [0 .. n - 1]
          ]
   in dMu - dNu + quad

-- | Ricci @R_{σν} = R^ρ_{σρν}@.
ricciDiagonal ::
  (Field a, FromInteger a) =>
  DiagonalMetric a ->
  [a] ->
  Int ->
  Int ->
  a
ricciDiagonal m x sigma nu =
  let n = dmDim m
   in sum [riemannDiagonal m x rho sigma rho nu | rho <- [0 .. n - 1]]
