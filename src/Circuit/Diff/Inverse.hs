{-# LANGUAGE RebindableSyntax #-}

-- | Inverse and implicit functions via Newton iteration on 'Diff'.
--
-- These are first-order theorems in action: the inverse-function theorem
-- says @(f⁻¹)'(f(a)) = 1/f'(a)@, and the implicit-function theorem says
-- @dy/dx = -(∂F/∂y)⁻¹ · ∂F/∂x@.  We use those derivatives (pulled back by
-- 'Diff') to drive Newton steps, and verify against exact oracles.
module Circuit.Diff.Inverse
  ( -- * Newton iteration
    newton,
    inverseN,
    implicit1N,

    -- * Primitives
    varDiff,
    constDiff,
  )
where

import Circuit.Diff (Diff (..), runDiff)
import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Prelude

-- | The identity differentiable function @x ↦ x@.
varDiff :: Diff p a a
varDiff = Diff (\s -> (s, id))

-- | Constant differentiable function.
constDiff :: (Additive a) => b -> Diff p a b
constDiff b = Diff (const (b, const zero))

-- | Newton iteration for solving @f(x) = target@.
--
-- @newton f target x0 n@ takes @n@ steps starting from @x0@.
newton ::
  (Subtractive a, Divisive a) =>
  Diff p a a ->
  a ->
  a ->
  Int ->
  a
newton f target x0 n =
  let step x =
        let (y, pb) = runDiff f x
            dy = pb one
         in x - (y - target) / dy
   in (!! n) (iterate step x0)

-- | Newton iteration for the inverse value: find @x@ such that @f(x) = y@.
inverseN ::
  (Subtractive a, Divisive a) =>
  Diff p a a ->
  a ->
  a ->
  Int ->
  a
inverseN f y = newton f y

-- | Newton iteration for a scalar implicit equation: find @y@ such that
-- @g(y) = 0@.  The caller fixes any ambient parameters (e.g. @x@ in
-- @F(x,y)=0@) by building them into @g@ with 'constDiff.
implicit1N ::
  (Subtractive b, Divisive b) =>
  Diff p b b ->
  b ->
  Int ->
  b
implicit1N g = newton g zero
