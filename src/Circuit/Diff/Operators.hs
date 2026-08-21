{-# LANGUAGE ScopedTypeVariables #-}

-- | Eshkol-style AD operators on top of the 'Circuit.Diff.Diff' carrier.
--
-- These are convenience wrappers around 'runDiff.  They expose a JAX-like
-- surface --- derivative, gradient, jacobian, hessian, divergence, curl,
-- laplacian --- while keeping the substrate's exact reverse-mode engine
-- underneath for first-order operators.
--
-- Higher-order scalar towers now use the 'Circuit.Diff.Taylor' carrier: a
-- 'Diff' function is sampled near the expansion point and a truncated Taylor
-- morphism is built from the finite-difference table.  This is an approximation
-- (the exact tower would require a dedicated forward-mode or Taylor-mode
-- carrier from the start), but it is enough to make 'derivativeN', 'taylor',
-- 'hessian' and 'laplacian' usable.
module Circuit.Diff.Operators
  ( -- * First-order operators
    derivative,
    gradient,
    jacobian,

    -- * Second-order operators
    hessian,
    divergence,
    curl,
    laplacian,

    -- * Higher-order towers (finite-difference bridge from Diff)
    derivativeN,
    taylor,

    -- * Exact higher-order towers (compositional Jet)
    derivativeNJ,
    taylorJ,
  )
where

import Circuit.Diff (Diff (..), runDiff)
import Circuit.Diff.Jet (Jet)
import Circuit.Diff.Jet qualified as Jet
import Circuit.Diff.Taylor (Taylor, approxTaylorFromDiff, evalTaylor)
import Data.Proxy (Proxy)
import GHC.TypeNats (SomeNat (..), someNatVal)
import Numeric.Natural (Natural)
import Prelude

-- $setup
-- >>> import Circuit.Diff (Diff (..))

-- | Scalar derivative: @f : R -> R@ at @x@.
--
-- >>> let sq = Diff (\x -> (x * x, \d -> 2 * x * d)) :: Diff () Double Double
-- >>> derivative sq 3.0
-- 6.0
derivative :: Diff p Double Double -> Double -> Double
derivative f x =
  let (_, pb) = runDiff f x
   in pb 1.0

-- | Gradient of a scalar function: @f : R^n -> R@ at @v@.
--
-- Returns the vector @∇f(v)@ by applying the pullback to the unit scalar.
gradient :: Diff p [Double] Double -> [Double] -> [Double]
gradient f v =
  let (_, pb) = runDiff f v
   in pb 1.0

-- | Jacobian of a vector function: @f : R^n -> R^m@ at @v@.
--
-- Returns an @m × n@ matrix: outer index is output component, inner index is
-- input component.  Each row is obtained by applying the pullback to one
-- output basis vector.
jacobian :: Diff p [Double] [Double] -> [Double] -> [[Double]]
jacobian f v =
  let (y, pb) = runDiff f v
      m = length y
      basis i = [if j == i then 1.0 else 0.0 | j <- [0 .. m - 1]]
   in [pb (basis i) | i <- [0 .. m - 1]]

-- | Trace of the Jacobian: @div f v = Σ_i ∂f_i/∂x_i@.
divergence :: Diff p [Double] [Double] -> [Double] -> Double
divergence f v =
  let j = jacobian f v
      n = length v
   in sum [j !! i !! i | i <- [0 .. n - 1]]

-- | Curl of a 3-D vector field: @f : R^3 -> R^3@ at @v@.
curl :: Diff p [Double] [Double] -> [Double] -> [Double]
curl f v =
  let j = jacobian f v
      at r c = (j !! r) !! c
   in [ at 2 1 - at 1 2,
        at 0 2 - at 2 0,
        at 1 0 - at 0 1
      ]

-- | Hessian of a scalar function: @f : R^n -> R@ at @v@.
--
-- Implemented by central second-order finite differences; approximate.
hessian :: Diff p [Double] Double -> [Double] -> [[Double]]
hessian f v =
  let n = length v
      h = 1e-4 * max 1.0 (sqrt (sum (map (^ (2 :: Int)) v)))
      e i = [if j == i then h else 0.0 | j <- [0 .. n - 1]]
      val u = fst (runDiff f u)
      fij i j =
        ( val (zipWith (+) v (zipWith (+) (e i) (e j)))
            - val (zipWith (+) v (e i))
            - val (zipWith (+) v (e j))
            + val v
        )
          / (h * h)
   in [[fij i j | j <- [0 .. n - 1]] | i <- [0 .. n - 1]]

-- | Laplacian of a scalar function: @f : R^n -> R@ at @v@.
--
-- Trace of the finite-difference Hessian.
laplacian :: Diff p [Double] Double -> [Double] -> Double
laplacian f v =
  let h = hessian f v
      n = length v
   in sum [h !! i !! i | i <- [0 .. n - 1]]

-- | N-th derivative of a scalar function: @f : R -> R@ at @x@.
--
-- For @n <= 1@ this is exact reverse-mode AD.  Higher orders are read from
-- a finite-difference Taylor tower built with 'Circuit.Diff.Taylor'.
derivativeN :: Diff p Double Double -> Double -> Int -> Double
derivativeN f x 0 = fst (runDiff f x)
derivativeN f x n
  | n < 0 = error "derivativeN: negative order"
  | otherwise = taylor f x n !! n

-- | First @k@ raw derivatives of @f : R -> R@ at @x0@.
--
-- The result is @[f(x0), f'(x0), f''(x0), ..., f^(k)(x0)]@.  The constant
-- and linear terms are exact; higher terms come from a finite-difference
-- Taylor tower built with 'Circuit.Diff.Taylor'.
taylor :: Diff p Double Double -> Double -> Int -> [Double]
taylor _ _ k | k < 0 = error "taylor: negative order"
taylor f x0 k =
  case someNatVal (fromIntegral k :: Natural) of
    SomeNat (_ :: Proxy n) ->
      let cs = evalTaylor (approxTaylorFromDiff f x0 :: Taylor n Double Double) 0
          facts = scanl (*) 1.0 [1.0 .. fromIntegral k]
       in zipWith (*) cs facts

-- | Exact N-th derivative of a scalar function expressed as a compositional
-- 'Circuit.Diff.Jet' tower.
--
-- The function must be built from NumHask-polymorphic operations; the tower is
-- propagated by the closed recurrences in 'Circuit.Diff.Jet'.  There is no
-- finite-difference approximation.
derivativeNJ :: (Jet Double -> Jet Double) -> Double -> Int -> Double
derivativeNJ f x n
  | n < 0 = error "derivativeNJ: negative order"
  | otherwise = taylorJ f x n !! n

-- | Exact first @k@ raw derivatives via a compositional 'Circuit.Diff.Jet'
-- tower.
taylorJ :: (Jet Double -> Jet Double) -> Double -> Int -> [Double]
taylorJ f x k
  | k < 0 = error "taylorJ: negative order"
  | otherwise = Jet.taylor f k x
