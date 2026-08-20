{-# LANGUAGE RebindableSyntax #-}

-- | Charts interpreted as differentiable maps and the geometry they induce.
--
-- A chart @φ : U ⊂ ℝⁿ → M@ pulls the Euclidean metric on @M@ back to a
-- coordinate metric @g = JᵀJ@.  From that metric we can raise/lower indices
-- and compute Christoffel symbols / covariant derivatives — the standard
-- differential-geometry pipeline, using the 'Diff' pullback as the Jacobian.
module Circuit.Diff.Chart
  ( -- * Chart as a differentiable map
    polarChartDiff,

    -- * Induced metric
    inducedMetric2D,
    raise2D,
    polarMetricLower,
    polarMetricRaise,

    -- * Levi-Civita connection from a 2D metric
    partialG,
    christoffel2D,
    directionalDerivative,
    covariantDerivative,
  )
where

import Circuit.Diff (Diff (..), Diff', runDiff)
import NumHask.Prelude
import Prelude ()

-- | Dot product on ℝ².
dot2 :: (Additive a, Multiplicative a) => (a, a) -> (a, a) -> a
dot2 (x1, y1) (x2, y2) = x1 * x2 + y1 * y2

-- | Pull back the Euclidean metric through a 2-D differentiable chart.
--
-- For a chart @φ@ with Jacobian @J@, the induced metric is @g(v) = Jᵀ J v@.
-- The backward pass of the returned 'Diff is zero because the typical consumer
-- (an optimizer or connection computation) does not back-propagate through the
-- metric coefficients.
inducedMetric2D ::
  (Additive a, Multiplicative a) =>
  Diff' (a, a) (a, a) ->
  Diff' ((a, a), (a, a)) (a, a)
inducedMetric2D (Diff f) = Diff $ \(x, v) ->
  let (_, jt) = f x
      jv1 = dot2 v (jt (one, zero))
      jv2 = dot2 v (jt (zero, one))
      gv = jt (jv1, jv2)
   in (gv, const ((zero, zero), (zero, zero)))

-- | Invert a 2-D metric 'Diff to obtain the raising operation @g⁻¹@.
raise2D :: (Field a) => Diff' ((a, a), (a, a)) (a, a) -> Diff' ((a, a), (a, a)) (a, a)
raise2D (Diff lower) = Diff $ \(x, c) ->
  let (col1, _) = lower (x, (one, zero))
      (col2, _) = lower (x, (zero, one))
      g00 = fst col1
      g10 = snd col1
      g01 = fst col2
      g11 = snd col2
      det = g00 * g11 - g01 * g10
      inv00 = g11 / det
      inv01 = negate g01 / det
      inv10 = negate g10 / det
      inv11 = g00 / det
      v1 = inv00 * fst c + inv01 * snd c
      v2 = inv10 * fst c + inv11 * snd c
   in ((v1, v2), const ((zero, zero), (zero, zero)))

-- | Polar coordinates @(r, θ)@ to cartesian @(x, y)@ as a 'Diff.
polarChartDiff :: (TrigField a) => Diff' (a, a) (a, a)
polarChartDiff = Diff $ \(r, theta) ->
  let c = cos theta
      s = sin theta
      x = r * c
      y = r * s
   in ( (x, y),
        \(dx, dy) -> (dx * c + dy * s, r * (dy * c - dx * s))
      )

-- | Polar coordinate metric @g = diag(1, r²)@ derived from 'polarChartDiff.
--
-- The pullback is honest: it carries @∂g@ in the point-slot so that
-- 'christoffel2D' can recover the Levi-Civita connection.
polarMetricLower :: (TrigField a) => Diff' ((a, a), (a, a)) (a, a)
polarMetricLower = Diff $ \((r, _), (vr, vtheta)) ->
  let tw = one + one
   in ( (vr, r * r * vtheta),
        \(dcr, dctheta) ->
          ( (tw * r * vtheta * dctheta, zero),
            (dcr, r * r * dctheta)
          )
      )

-- | Polar coordinate inverse metric @g⁻¹ = diag(1, 1/r²)@.
polarMetricRaise :: (TrigField a) => Diff' ((a, a), (a, a)) (a, a)
polarMetricRaise = raise2D polarMetricLower

-- | Basis vectors in ℝ².
basis0 :: (Additive a, Multiplicative a) => (a, a)
basis0 = (one, zero)

basis1 :: (Additive a, Multiplicative a) => (a, a)
basis1 = (zero, one)

-- | Extract the partial derivatives @∂ᵢ gⱼₖ@ of a 2-D metric from its own
-- 'Diff pullback.
partialG ::
  (Additive a, Multiplicative a) =>
  Diff' ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  (((a, a), (a, a)), ((a, a), (a, a)))
partialG lower x =
  let probe v dc =
        let (_, back) = runDiff lower (x, v)
            (dpoint, _) = back dc
         in dpoint
      row0 = (probe basis0 basis0, probe basis0 basis1)
      row1 = (probe basis1 basis0, probe basis1 basis1)
   in (row0, row1)

-- | Christoffel symbols @Γᶜₐᵦ@ of a 2-D metric from @∂g@ and @g⁻¹@.
--
-- Uses @Γᶜₐᵦ = ½ gᶜⁱ(∂ₐ gᵢᵦ + ∂ᵦ gᵢₐ − ∂ᵢ gₐᵦ)@.
christoffel2D ::
  forall a.
  (Field a) =>
  Diff' ((a, a), (a, a)) (a, a) ->
  Diff' ((a, a), (a, a)) (a, a) ->
  (a, a) ->
  (a, a, a, a, a, a, a, a)
christoffel2D lower raise x =
  let pg = partialG lower x
      ((g00, g01), (g10, g11)) =
        let (v0, _) = runDiff raise (x, basis0)
            (v1, _) = runDiff raise (x, basis1)
         in (v0, v1)
      d :: Int -> Int -> Int -> a
      d i j k = case (i, j, k) of
        (0, 0, 0) -> fst (fst (fst pg))
        (0, 0, 1) -> fst (snd (fst pg))
        (0, 1, 0) -> fst (fst (snd pg))
        (0, 1, 1) -> fst (snd (snd pg))
        (1, 0, 0) -> snd (fst (fst pg))
        (1, 0, 1) -> snd (snd (fst pg))
        (1, 1, 0) -> snd (fst (snd pg))
        (1, 1, 1) -> snd (snd (snd pg))
        _ -> error "christoffel2D: index out of range"
      gamma :: Int -> Int -> Int -> a
      gamma c a b =
        (one / (one + one))
          * ( (if c == (0 :: Int) then g00 else g10)
                * (d a 0 b + d b 0 a - d 0 a b)
                + (if c == (0 :: Int) then g01 else g11)
                * (d a 1 b + d b 1 a - d 1 a b)
            )
   in ( gamma 0 0 0,
        gamma 0 0 1,
        gamma 0 1 0,
        gamma 0 1 1,
        gamma 1 0 0,
        gamma 1 0 1,
        gamma 1 1 0,
        gamma 1 1 1
      )

-- | Directional derivative of a vector field from its 'Diff' pullback.
directionalDerivative ::
  (Additive a, Multiplicative a) =>
  Diff' (a, a) (a, a) ->
  (a, a) ->
  (a, a) ->
  (a, a)
directionalDerivative v x dx =
  let (_, vt) = runDiff v x
      vTe0 = vt basis0
      vTe1 = vt basis1
   in ( fst dx * fst vTe0 + snd dx * snd vTe0,
        fst dx * fst vTe1 + snd dx * snd vTe1
      )

-- | Covariant derivative @∇_dx V = ∂_dx V + Γ(x)(dx, V(x))@.
covariantDerivative ::
  (Field a) =>
  Diff' ((a, a), (a, a)) (a, a) ->
  Diff' ((a, a), (a, a)) (a, a) ->
  Diff' (a, a) (a, a) ->
  (a, a) ->
  (a, a) ->
  (a, a)
covariantDerivative lower raise v x dx =
  let (vx, _) = runDiff v x
      (g000, g001, g010, g011, g100, g101, g110, g111) = christoffel2D lower raise x
      dx0 = fst dx
      dx1 = snd dx
      v0 = fst vx
      v1 = snd vx
      gamma0 = g000 * dx0 * v0 + g001 * dx0 * v1 + g010 * dx1 * v0 + g011 * dx1 * v1
      gamma1 = g100 * dx0 * v0 + g101 * dx0 * v1 + g110 * dx1 * v0 + g111 * dx1 * v1
      partial = directionalDerivative v x dx
   in (fst partial + gamma0, snd partial + gamma1)
