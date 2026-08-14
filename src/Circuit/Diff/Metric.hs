{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Metric-aware transpose for differentiable arrows.
--
-- A metric @g@ turns the bare dagger (transpose) of a 'Diff' into the true
-- adjoint @g_a^-1 . J^T . g_b@.  The same combinator also supports
-- optimizer-style preconditioning, where @g@ is a diagonal metric
-- @diag(sqrt v + eps)@ and only the lowering half is used.
module Circuit.Diff.Metric
  ( -- * Adjoint with respect to domain/codomain metrics
    adjointWith,

    -- * Forward-only metric application
    raiseWith,
    lowerWith,

    -- * Common metrics
    diagonalMetric,
    euclideanMetric,
  )
where

import Circuit.Diff (Diff, runDiff, pattern Diff)
import NumHask.Prelude
import Prelude ()

-- | Adjoint of @J : a -> b@ with respect to domain metric @g_a@ and
-- codomain metric @g_b@.
--
-- The metrics are themselves 'Diff's of type @Diff (point, vector) vector@:
-- the forward pass lowers or raises a vector at the given point.  The
-- backward pass of the metric carries @∂g@ in its point-slot; 'adjointWith'
-- uses only the forward passes.
adjointWith ::
  -- | @g_a^-1@ — raise a covector on the domain to a vector
  Diff (a, a) a ->
  -- | @g_b@ — lower a vector on the codomain to a covector
  Diff (b, b) b ->
  -- | @J : a -> b@
  Diff a b ->
  -- | @J@ with its pullback conjugated to the @g@-adjoint.  The type is
  -- still @Diff a b@ because the lens stores the forward map @a -> b@ and
  -- the backward map @b -> a@; the adjoint lives in the pullback.
  Diff a b
adjointWith raiseA lowerB (Diff f) = Diff $ \x ->
  let (y, jt) = f x
   in ( y,
        \db ->
          let (lowered, _) = runDiff lowerB (y, db)
              covectorA = jt lowered
              (raised, _) = runDiff raiseA (x, covectorA)
           in raised
      )

-- | Raise a covector using a metric at the given point.
raiseWith :: Diff (s, a) a -> s -> a -> a
raiseWith g s covec = fst (runDiff g (s, covec))

-- | Lower a vector using a metric at the given point.
lowerWith :: Diff (s, a) a -> s -> a -> a
lowerWith g s vec = fst (runDiff g (s, vec))

-- | Euclidean metric @g = δ@: raise and lower are both the identity.
euclideanMetric :: (Additive a) => Diff (a, a) a
euclideanMetric = Diff $ \(_, v) -> (v, const (zero, zero))

-- | Diagonal metric @g(s) = diag(f s)@.
--
-- Lowering maps @x -> f s * x@; raising maps @c -> recip (f s) * c@.
-- The pullback's state-slot is zero because the typical consumer (an
-- optimizer) does not back-propagate through the metric coefficients.
-- If you need Christoffel-style @∂g@, write a custom metric 'Diff'.
diagonalMetric ::
  (Additive s, Multiplicative a, Divisive a) =>
  -- | @f@ such that @g(s) = diag(f s)@
  (s -> a -> a) ->
  Diff (s, a) a
diagonalMetric f = Diff $ \(s, x) ->
  let gx = f s x
   in ( gx,
        \dc -> (zero, f s dc)
      )
