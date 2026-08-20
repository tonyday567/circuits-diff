{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

-- | Tensor AD on top of 'Harpie.Fixed.Array' and 'Circuit.Mat.Square'.
--
-- This module provides:
--
-- * forward-mode Taylor towers for square-matrix computations, via 'Jet'
--   instantiated at 'Square n Double';
-- * elementwise towers by mapping scalar 'Jet's across array elements;
-- * explicit reverse-mode 'Diff'' primitives for matrix multiplication,
--   transpose, sum, scale, and elementwise activations.
--
-- The generic 'Multiplicative' instance of 'Diff'' is /not/ used for matrix
-- multiplication because its product-rule pullback is the wrong adjoint for
-- non-commutative multiplication.
module Circuit.Diff.Tensor
  ( -- * Forward-mode tensor towers
    tensorTaylor,
    tensorDerivativeN,
    elementwiseTower,

    -- * Reverse-mode tensor primitives
    matMulD,
    transposeD,
    sumD,
    scaleD,
    elementwiseD,
    sigmoidD,
    tanhD,
  )
where

import Circuit.Diff (Diff', pattern Diff)
import Circuit.Diff.Jet (Jet (..), taylorDers, variable)
import Circuit.Mat.Square (Square)
import Data.Foldable (foldl')
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat)
import Harpie.Fixed (Array)
import Harpie.Fixed qualified as F
import Harpie.Shape (KnownNats)
import NumHask.Algebra.Additive (Additive (..), Subtractive (..))
import NumHask.Algebra.Field (ExpField (..), TrigField (..))
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..), recip)
import NumHask.Data.Integral (FromInteger (..))
import Prelude hiding (abs, cos, exp, fromInteger, fromRational, log, recip, sin, sqrt, tanh, (/), (*), (+), (-))
import Prelude qualified as P

-- ---------------------------------------------------------------------------
-- Forward-mode tensor towers
-- ---------------------------------------------------------------------------

-- | First @k@ raw derivatives of a square-matrix function at @x0@.
--
-- The function must be built from NumHask-polymorphic operations so that the
-- 'Jet' recurrence engine can propagate matrix coefficients through matrix
-- multiplication.
tensorTaylor ::
  forall n a.
  ( KnownNat n,
    Additive a,
    Multiplicative a,
    FromInteger a
  ) =>
  (Jet (Square n a) -> Jet (Square n a)) ->
  Int ->
  Square n a ->
  [Square n a]
tensorTaylor f k x0 = taylorDers (f (variable k x0))

-- | The @n@-th raw derivative of a square-matrix function at @x0@.
tensorDerivativeN ::
  forall n a.
  ( KnownNat n,
    Additive a,
    Multiplicative a,
    FromInteger a
  ) =>
  (Jet (Square n a) -> Jet (Square n a)) ->
  Int ->
  Square n a ->
  Square n a
tensorDerivativeN f n x0 = tensorTaylor f n x0 !! n

-- | Apply a scalar tower function elementwise to every entry of an array.
--
-- This is the elementwise analogue of Eshkol's @tt-sigmoid@ / @tt-tanh@:
-- each component gets its own scalar Taylor tower, independent of the others.
elementwiseTower ::
  forall s a.
  ( KnownNats s,
    Additive a,
    Multiplicative a,
    FromInteger a
  ) =>
  (Jet a -> Jet a) ->
  Int ->
  Array s a ->
  Array s a
elementwiseTower f k arr =
  F.tabulate $ \ix ->
    let x = F.index arr ix
     in taylorDers (f (variable k x)) !! k

-- ---------------------------------------------------------------------------
-- Reverse-mode tensor primitives
-- ---------------------------------------------------------------------------

-- | Matrix multiplication with the correct reverse-mode adjoint.
--
-- For @Y = A B@ the pullback is @dA = dY B^T@, @dB = A^T dY@.
matMulD ::
  forall n p.
  (KnownNat n) =>
  Diff' p (Square n Double, Square n Double) (Square n Double)
matMulD =
  Diff $ \(a, b) ->
    let y = a * b
        bt = F.transpose b
        at = F.transpose a
        pb db = (db * bt, at * db)
     in (y, pb)

-- | Transpose.  Its own adjoint.
transposeD ::
  forall m n p.
  (KnownNat m, KnownNat n) =>
  Diff' p (Array '[m, n] Double) (Array '[n, m] Double)
transposeD =
  Diff $ \a ->
    let y = F.transpose a
     in (y, F.transpose)

-- | Sum all elements of an array.  Pullback replicates the scalar.
sumD ::
  forall s p.
  (KnownNats s) =>
  Diff' p (Array s Double) Double
sumD =
  Diff $ \a ->
    let y = foldl' (+) zero a
     in (y, \db -> F.konst db)

-- | Scale every element by a constant.
scaleD ::
  forall s p.
  Double ->
  Diff' p (Array s Double) (Array s Double)
scaleD s =
  Diff $ \a ->
    let y = fmap (s *) a
     in (y, \db -> fmap (s *) db)

-- | Elementwise activation from a scalar primitive @x -> (y, dy/dx)@.
elementwiseD ::
  forall s p.
  (KnownNats s) =>
  (Double -> (Double, Double -> Double)) ->
  Diff' p (Array s Double) (Array s Double)
elementwiseD phi =
  Diff $ \a ->
    let (ys, grads) = unzipA (fmap phi a)
        pb db = F.zipWith (\g dbi -> g dbi) grads db
     in (ys, pb)

-- | Sigmoid activation.
sigmoidD ::
  forall s p.
  (KnownNats s) =>
  Diff' p (Array s Double) (Array s Double)
sigmoidD = elementwiseD $ \x ->
  let s = recip (1 + exp (-x))
   in (s, \db -> db * s * (1 - s))

-- | Tanh activation.
tanhD ::
  forall s p.
  (KnownNats s) =>
  Diff' p (Array s Double) (Array s Double)
tanhD = elementwiseD $ \x ->
  let t = tanh x
   in (t, \db -> db * (1 - t * t))

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

-- Split an array of @(value, derivative-function)@ pairs into two arrays.
unzipA ::
  Array s (a, b) ->
  (Array s a, Array s b)
unzipA ab =
  ( fmap fst ab,
    fmap snd ab
  )
