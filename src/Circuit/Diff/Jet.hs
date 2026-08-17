{-# LANGUAGE RebindableSyntax #-}

-- | Jets via truncated Taylor series.
--
-- A 'Jet' is a finite tower of Taylor coefficients
--
-- > c0 + c1*h + c2*h^2 + ... + cn*h^n
--
-- around a primal point.  Elementary functions act coefficient-wise via the
-- usual dual-number recurrences, so a NumHask-polymorphic function
-- @f :: (ExpField a, TrigField a) => a -> a@ applied to @'variable' n a@
-- returns the first @n+1@ Taylor coefficients of @f@ at @a@.
--
-- This is the "iterated" direction of @Diff'@: where @Diff'@ carries one
-- pullback, a jet carries the whole truncated tower.  The two interoperate
-- through 'jetFromDiff', which seeds the tower from a first-order pullback.
module Circuit.Diff.Jet
  ( -- * Jet type
    Jet (..),
    jetOrder,

    -- * Construction
    variable,
    constant,
    fromDiff,

    -- * Coefficient views
    taylorDers,
    taylor,

    -- * Series operations
    differentiate,
    integrate,
    scale,
    resize,
  )
where

import Circuit.Diff (Diff', runDiff)
import NumHask.Algebra.Additive (Additive (..), Subtractive (..), sum)
import NumHask.Algebra.Field (ExpField (..), TrigField (..))
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Data.Integral (FromInteger (..))
import Prelude hiding (acos, asin, atan, atan2, cos, exp, fromInteger, log, negate, pi, recip, sin, sqrt, sum, (*), (+), (-), (/))
import Prelude qualified as P

-- | Truncated Taylor series stored as coefficients @[c0, c1, ..., cn]@
-- representing @c0 + c1*h + c2*h^2 + ... + cn*h^n@.
newtype Jet a = Jet {coefficients :: [a]}
  deriving (Eq, Show)

-- | Highest power of @h@ present.
jetOrder :: Jet a -> Int
jetOrder = P.pred . P.length . coefficients

-- | Truncate / pad to the given order.
resize :: (Additive a) => Int -> Jet a -> Jet a
resize n (Jet cs) = Jet $ P.take (n P.+ 1) (cs P.++ P.repeat zero)

-- | Align two jets to the same order by truncating the higher one.
align :: Jet a -> Jet a -> ([a], [a])
align (Jet xs) (Jet ys) =
  let n = P.min (P.length xs) (P.length ys)
   in (P.take n xs, P.take n ys)

-- | Align two jets, lifting a length-1 (constant) jet to the order of the
-- other by padding with zeros.  This makes @one@, @zero@ and numeric literals
-- behave as scalars of arbitrary order.
alignLift :: (Additive a) => Jet a -> Jet a -> ([a], [a])
alignLift (Jet [x]) (Jet ys) = (x : P.replicate (P.length ys - 1) zero, ys)
alignLift (Jet xs) (Jet [y]) = (xs, y : P.replicate (P.length xs - 1) zero)
alignLift (Jet xs) (Jet ys) = align (Jet xs) (Jet ys)

-- | Build a jet of order @n@ representing the input variable @a + h@.
variable :: (Additive a, Multiplicative a) => Int -> a -> Jet a
variable n a = Jet (a : one : P.replicate (n P.- 1) zero)

-- | Build a constant jet of order @n@.
constant :: (Additive a) => Int -> a -> Jet a
constant n c = Jet (c : P.replicate n zero)

-- | Seed a first-order jet from a 'Diff'' first derivative.
--
-- Higher derivatives are /not/ recovered from a bare 'Diff''; use 'taylor'
-- with a NumHask-polymorphic function for automatic higher-order towers.
fromDiff :: (Multiplicative a) => Diff' p a a -> a -> Jet a
fromDiff f a =
  let (y, pb) = runDiff f a
   in Jet [y, pb one]

-- | Convert Taylor coefficients to raw derivatives.
--
-- > taylorDers (Jet [c0, c1, c2]) = [c0, 1!*c1, 2!*c2]
taylorDers :: (Additive a, Multiplicative a, FromInteger a) => Jet a -> [a]
taylorDers (Jet cs) = P.zipWith (*) cs factorials
  where
    factorials = P.scanl (*) one (P.map (one +) (P.map fromInteger [(0 :: P.Integer) ..]))

-- | Apply a jet-level function at a point and return the raw
-- derivatives @[f(a), f'(a), f''(a), ..., f^(n)(a)]@.
taylor ::
  (ExpField a, FromInteger a) =>
  (Jet a -> Jet a) ->
  Int ->
  a ->
  [a]
taylor f n a = taylorDers (f (variable n a))

-- ---------------------------------------------------------------------------
-- NumHask instances
-- ---------------------------------------------------------------------------

instance (Additive a) => Additive (Jet a) where
  zero = Jet [zero]
  Jet xs + Jet ys =
    let (xs', ys') = alignLift (Jet xs) (Jet ys)
     in Jet (P.zipWith (+) xs' ys')

instance (Subtractive a) => Subtractive (Jet a) where
  negate (Jet xs) = Jet (P.map negate xs)
  Jet xs - Jet ys =
    let (xs', ys') = alignLift (Jet xs) (Jet ys)
     in Jet (P.zipWith (-) xs' ys')

instance (Additive a, Multiplicative a) => Multiplicative (Jet a) where
  one = Jet [one]
  Jet [c] * Jet ys = Jet (P.map (c *) ys)
  Jet xs * Jet [c] = Jet (P.map (* c) xs)
  Jet xs * Jet ys =
    let n = P.min (P.length xs) (P.length ys)
        cauchy k = sum [xs P.!! i * ys P.!! (k - i) | i <- [0 .. k]]
     in Jet [cauchy k | k <- [0 .. n - 1]]

-- | Reciprocal series via long division.
--
-- If @u = u0 + u1*h + ...@ and @v = 1/u = v0 + v1*h + ...@ then
-- @v0 = 1/u0@ and @vk = -(sum_{i=1}^k ui * v{k-i}) / u0@.
recipSeries ::
  (Subtractive a, Divisive a) =>
  [a] ->
  [a]
recipSeries [] = []
recipSeries (u0 : us) =
  let vs = P.map go [0 ..]
      go 0 = recip u0
      go k = negate (sum [us P.!! (i - 1) * vs P.!! (k - i) | i <- [1 .. k]]) / u0
   in vs

instance
  (Additive a, Subtractive a, Multiplicative a, Divisive a) =>
  NumHask.Algebra.Multiplicative.Divisive (Jet a)
  where
  recip (Jet xs) = Jet (P.take (P.length xs) (recipSeries xs))

-- ---------------------------------------------------------------------------
-- Field instances (exp / log / trig)
-- ---------------------------------------------------------------------------

-- | Term-by-term differentiation of a Taylor series.
--
-- > differentiate (Jet [c0, c1, c2, c3]) = Jet [c1, 2*c2, 3*c3]
differentiate ::
  (Multiplicative a, FromInteger a) =>
  Jet a ->
  Jet a
differentiate (Jet cs) =
  Jet [fromInteger (P.toInteger (k :: P.Int)) * c | (k, c) <- P.zip [(1 :: P.Int) ..] (P.drop 1 cs)]

-- | Term-by-term integration with supplied constant.
--
-- > integrate c0 (Jet [d0, d1, d2]) = Jet [c0, d0, d1/2, d2/3]
integrate ::
  (Divisive a, FromInteger a) =>
  a ->
  Jet a ->
  Jet a
integrate c0 (Jet ds) =
  Jet (c0 : [d / fromInteger (P.toInteger (k :: P.Int)) | (k, d) <- P.zip [(1 :: P.Int) ..] ds])

-- | Scale every coefficient by a scalar.
scale :: (Multiplicative a) => a -> Jet a -> Jet a
scale s (Jet cs) = Jet (P.map (s *) cs)

-- | Simultaneously compute the Taylor coefficients of sin(u) and cos(u)
-- around a primal point @u0@, using the recurrences
-- @m s_m = sum_{j=0}^{m-1} (m-j) c_j u_{m-j}@ and
-- @m c_m = -sum_{j=0}^{m-1} (m-j) s_j u_{m-j}@.
sinCosSeries ::
  (TrigField a, FromInteger a) =>
  a ->
  [a] ->
  (Jet a, Jet a)
sinCosSeries u0 us =
  let n = P.length us
      pairs = P.map go [0 .. n]
      go 0 = (sin u0, cos u0)
      go m =
        let m' = fromInteger (P.toInteger m)
            sSum = sum [fromInteger (P.toInteger (m - j)) * (snd (pairs P.!! j)) * (us P.!! (m - j - 1)) | j <- [0 .. m - 1]]
            cSum = sum [fromInteger (P.toInteger (m - j)) * (fst (pairs P.!! j)) * (us P.!! (m - j - 1)) | j <- [0 .. m - 1]]
         in ((one / m') * sSum, negate (one / m') * cSum)
      (ss, cs) = P.unzip pairs
   in (Jet ss, Jet cs)

-- | Square-root series via coefficient matching.
--
-- If @u = v²@ with @u = u0 + u1*h + ...@ and @v = v0 + v1*h + ...@ then
-- @v0 = sqrt(u0)@ and @vk = (uk - sum_{i=1}^{k-1} vi v{k-i}) / (2 v0)@.
sqrtSeries ::
  (ExpField a) =>
  [a] ->
  [a]
sqrtSeries [] = []
sqrtSeries (u0 : us) =
  let v0 = sqrt u0
      twoV0 = v0 + v0
      n = P.length us
      vs = P.map go [0 .. n]
      go 0 = v0
      go k =
        let inner = sum [vs P.!! i * vs P.!! (k - i) | i <- [1 .. k - 1]]
         in (us P.!! (k - 1) - inner) / twoV0
   in vs

instance (FromInteger a) => FromInteger (Jet a) where
  fromInteger n = Jet [fromInteger n]

instance (Subtractive a, Divisive a, ExpField a, FromInteger a) => ExpField (Jet a) where
  exp (Jet []) = Jet []
  exp (Jet (u0 : us)) =
    let -- Solve v' = v * u' with v0 = exp(u0) coefficient-wise.
        n = P.length us
        vs = P.map go [0 .. n]
        go 0 = exp u0
        go m =
          let m' = fromInteger (P.toInteger m)
           in (one / m') * sum [fromInteger (P.toInteger (m - j)) * (vs P.!! j) * (us P.!! (m - j - 1)) | j <- [0 .. m - 1]]
     in Jet vs

  log (Jet []) = Jet []
  log (Jet (u0 : us)) =
    let u = Jet (u0 : us)
     in integrate (log u0) (differentiate u / u)

  sqrt (Jet []) = Jet []
  sqrt (Jet xs) = Jet (P.take (P.length xs) (sqrtSeries xs))

instance (Subtractive a, Divisive a, ExpField a, TrigField a, FromInteger a) => TrigField (Jet a) where
  pi = Jet [pi]

  sin (Jet []) = Jet []
  sin (Jet (u0 : us)) =
    let (ss, _) = sinCosSeries u0 us
     in ss

  cos (Jet []) = Jet []
  cos (Jet (u0 : us)) =
    let (_, cs) = sinCosSeries u0 us
     in cs

  asin (Jet []) = Jet []
  asin (Jet (u0 : us)) =
    let u = Jet (u0 : us)
     in integrate (asin u0) (differentiate u / sqrt (one - u * u))

  acos (Jet []) = Jet []
  acos (Jet (u0 : us)) =
    let u = Jet (u0 : us)
     in integrate (acos u0) (negate (differentiate u / sqrt (one - u * u)))

  atan (Jet []) = Jet []
  atan (Jet (u0 : us)) =
    let u = Jet (u0 : us)
     in integrate (atan u0) (differentiate u / (one + u * u))

  atan2 y x =
    let y0 = headCoeff y
        x0 = headCoeff x
        deriv = (x * differentiate y - y * differentiate x) / (x * x + y * y)
     in integrate (atan2 y0 x0) deriv

  sinh u = (exp u - exp (negate u)) / (one + one)
  cosh u = (exp u + exp (negate u)) / (one + one)

  asinh u = log (u + sqrt (u * u + one))
  acosh u = log (u + sqrt (u * u - one))
  atanh u = log ((one + u) / (one - u)) / (one + one)

-- | Constant coefficient of a jet.
headCoeff :: Jet a -> a
headCoeff (Jet []) = P.error "Circuit.Diff.Jet.headCoeff: empty jet"
headCoeff (Jet (c : _)) = c
