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
-- This is the "iterated" direction of @Diff@: where @Diff@ carries one
-- pullback, a jet carries the whole truncated tower.  The two interoperate
-- through 'jetFromDiff, which seeds the tower from a first-order pullback.
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

import Circuit.Diff (Diff, runDiff)
import Circuit.Process qualified as CP (Process (..), scan)
import NumHask.Algebra.Additive (Additive (..), Subtractive (..), sum)
import NumHask.Algebra.Field (ExpField (..), TrigField (..))
import NumHask.Algebra.Multiplicative (Divisive (..), Multiplicative (..))
import NumHask.Data.Integral (FromInteger (..))
import NumHask.Prelude

-- | Truncated Taylor series stored as coefficients @[c0, c1, ..., cn]@
-- representing @c0 + c1*h + c2*h^2 + ... + cn*h^n@.
newtype Jet a = Jet {coefficients :: [a]}
  deriving (Eq, Show)

-- | Highest power of @h@ present.
jetOrder :: Jet a -> Int
jetOrder = pred . length . coefficients

-- | Truncate / pad to the given order.
resize :: (Additive a) => Int -> Jet a -> Jet a
resize n (Jet cs) = Jet $ take (n + 1) (cs ++ repeat zero)

-- | Align two jets to the same order by truncating the higher one.
align :: Jet a -> Jet a -> ([a], [a])
align (Jet xs) (Jet ys) =
  let n = min (length xs) (length ys)
   in (take n xs, take n ys)

-- | Align two jets, lifting a length-1 (constant) jet to the order of the
-- other by padding with zeros.  This makes @one@, @zero@ and numeric literals
-- behave as scalars of arbitrary order.
alignLift :: (Additive a) => Jet a -> Jet a -> ([a], [a])
alignLift (Jet [x]) (Jet ys) = (x : replicate (length ys - 1) zero, ys)
alignLift (Jet xs) (Jet [y]) = (xs, y : replicate (length xs - 1) zero)
alignLift (Jet xs) (Jet ys) = align (Jet xs) (Jet ys)

-- | Build a jet of order @n@ representing the input variable @a + h@.
variable :: (Additive a, Multiplicative a) => Int -> a -> Jet a
variable n a = Jet (a : one : replicate (n - 1) zero)

-- | Build a constant jet of order @n@.
constant :: (Additive a) => Int -> a -> Jet a
constant n c = Jet (c : replicate n zero)

-- | Seed a first-order jet from a 'Diff' first derivative.
--
-- Higher derivatives are /not/ recovered from a bare 'Diff'; use 'taylor'
-- with a NumHask-polymorphic function for automatic higher-order towers.
fromDiff :: (Multiplicative a) => Diff p a a -> a -> Jet a
fromDiff f a =
  let (y, pb) = runDiff f a
   in Jet [y, pb one]

-- | Convert Taylor coefficients to raw derivatives.
--
-- > taylorDers (Jet [c0, c1, c2]) = [c0, 1!*c1, 2!*c2]
taylorDers :: (Additive a, Multiplicative a, FromInteger a) => Jet a -> [a]
taylorDers (Jet cs) = zipWith (*) cs factorials
  where
    factorials = scanl (*) one (map ((one +) . fromInteger) [(0 :: Integer) ..])

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
     in Jet (zipWith (+) xs' ys')

instance (Subtractive a) => Subtractive (Jet a) where
  negate (Jet xs) = Jet (map negate xs)
  Jet xs - Jet ys =
    let (xs', ys') = alignLift (Jet xs) (Jet ys)
     in Jet (zipWith (-) xs' ys')

instance (Additive a, Multiplicative a) => Multiplicative (Jet a) where
  one = Jet [one]
  Jet [c] * Jet ys = Jet (map (c *) ys)
  Jet xs * Jet [c] = Jet (map (* c) xs)
  Jet xs * Jet ys =
    let n = min (length xs) (length ys)
        cauchy k = sum [xs !! i * ys !! (k - i) | i <- [0 .. k]]
     in Jet [cauchy k | k <- [0 .. n - 1]]

-- | Tail process for the reciprocal series.
--
-- If @u = u0 + u1*h + ...@ and @v = 1/u = v0 + v1*h + ...@ then
-- @v0 = 1/u0@ and @vk = -(sum_{i=1}^k ui * v{k-i}) / u0@.
-- The process consumes @u1, u2, ...@ and emits @v1, v2, ...@; the caller
-- prepends @v0@.
recipTailProcess ::
  (Subtractive a, Divisive a) =>
  a ->
  CP.Process a a
recipTailProcess u0 =
  CP.Process inject step extract
  where
    v0 = recip u0
    inject u = step ([v0], []) u
    step (vs, us) u =
      let k = length vs
          us' = us ++ [u]
          vk = negate (sum [us' !! (i - 1) * vs !! (k - i) | i <- [1 .. k]]) / u0
       in (vs ++ [vk], us')
    extract (vs, _) = last vs

-- | Reciprocal series as a coinductive stream.
--
-- @recipSeries u0 us@ produces @[v0, v1, ...]@ for @us = [u1, u2, ...]@.
-- The output length is one more than the input length, so truncation is
-- decided by the caller.
recipSeries ::
  (Subtractive a, Divisive a) =>
  a ->
  [a] ->
  [a]
recipSeries u0 us = recip u0 : CP.scan (recipTailProcess u0) us

instance
  (Additive a, Subtractive a, Multiplicative a, Divisive a) =>
  NumHask.Algebra.Multiplicative.Divisive (Jet a)
  where
  recip (Jet []) = Jet []
  recip (Jet (u0 : us)) = Jet (recipSeries u0 us)

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
  Jet [fromInteger (fromIntegral (k :: Int)) * c | (k, c) <- zip [(1 :: Int) ..] (drop 1 cs)]

-- | Term-by-term integration with supplied constant.
--
-- > integrate c0 (Jet [d0, d1, d2]) = Jet [c0, d0, d1/2, d2/3]
integrate ::
  (Divisive a, FromInteger a) =>
  a ->
  Jet a ->
  Jet a
integrate c0 (Jet ds) =
  Jet (c0 : [d / fromInteger (fromIntegral (k :: Int)) | (k, d) <- zip [(1 :: Int) ..] ds])

-- | Scale every coefficient by a scalar.
scale :: (Multiplicative a) => a -> Jet a -> Jet a
scale s (Jet cs) = Jet (map (s *) cs)

-- | Tail process for the mutual sin/cos series.
--
-- Around a primal point @u0@, the recurrences are
-- @m s_m = sum_{j=0}^{m-1} (m-j) c_j u_{m-j}@ and
-- @m c_m = -sum_{j=0}^{m-1} (m-j) s_j u_{m-j}@.
-- The process consumes @u1, u2, ...@ and emits @(s1, c1), (s2, c2), ...@;
-- the caller prepends @(sin u0, cos u0)@.
sinCosTailProcess ::
  (TrigField a, FromInteger a) =>
  a ->
  CP.Process a (a, a)
sinCosTailProcess u0 =
  CP.Process inject step extract
  where
    s0 = sin u0
    c0 = cos u0
    inject u = step ([s0], [c0], []) u
    step (ss, cs, us) u =
      let k = length ss
          us' = us ++ [u]
          m' = fromInteger (fromIntegral k)
          sSum = sum [fromInteger (fromIntegral (k - j)) * (cs !! j) * (us' !! (k - 1 - j)) | j <- [0 .. k - 1]]
          cSum = sum [fromInteger (fromIntegral (k - j)) * (ss !! j) * (us' !! (k - 1 - j)) | j <- [0 .. k - 1]]
          sk = (one / m') * sSum
          ck = negate (one / m') * cSum
       in (ss ++ [sk], cs ++ [ck], us')
    extract (ss, cs, _) = (last ss, last cs)

-- | Simultaneously compute the Taylor coefficients of sin(u) and cos(u)
-- around a primal point @u0@.
sinCosSeries ::
  (TrigField a, FromInteger a) =>
  a ->
  [a] ->
  (Jet a, Jet a)
sinCosSeries u0 us =
  let pairs = (sin u0, cos u0) : CP.scan (sinCosTailProcess u0) us
      (ss, cs) = unzip pairs
   in (Jet ss, Jet cs)

-- | Tail process for the square-root series.
--
-- If @u = v²@ with @u = u0 + u1*h + ...@ and @v = v0 + v1*h + ...@ then
-- @v0 = sqrt(u0)@ and @vk = (uk - sum_{i=1}^{k-1} vi v{k-i}) / (2 v0)@.
-- The process consumes @u1, u2, ...@ and emits @v1, v2, ...@; the caller
-- prepends @v0@.
sqrtTailProcess ::
  (ExpField a) =>
  a ->
  CP.Process a a
sqrtTailProcess u0 =
  CP.Process inject step extract
  where
    v0 = sqrt u0
    twoV0 = v0 + v0
    inject u = step ([v0], []) u
    step (vs, us) u =
      let k = length vs
          us' = us ++ [u]
          inner = sum [vs !! i * vs !! (k - i) | i <- [1 .. k - 1]]
          vk = (us' !! (k - 1) - inner) / twoV0
       in (vs ++ [vk], us')
    extract (vs, _) = last vs

-- | Square-root series as a coinductive stream.
sqrtSeries ::
  (ExpField a) =>
  a ->
  [a] ->
  [a]
sqrtSeries u0 us = sqrt u0 : CP.scan (sqrtTailProcess u0) us

instance (FromInteger a) => FromInteger (Jet a) where
  fromInteger n = Jet [fromInteger n]

-- | Tail process for the exponential series.
--
-- Solves @v' = v * u'@ with @v0 = exp(u0)@ coefficient-wise:
-- @m v_m = sum_{j=0}^{m-1} (m-j) v_j u_{m-j}@.
-- The process consumes @u1, u2, ...@ and emits @v1, v2, ...@; the caller
-- prepends @v0@.
expTailProcess ::
  (ExpField a, FromInteger a) =>
  a ->
  CP.Process a a
expTailProcess u0 =
  CP.Process inject step extract
  where
    v0 = exp u0
    inject u = step ([v0], []) u
    step (vs, us) u =
      let m = length vs
          us' = us ++ [u]
          m' = fromInteger (fromIntegral m)
          vm =
            (one / m')
              * sum
                [ fromInteger (fromIntegral (m - j)) * (vs !! j) * (us' !! (m - 1 - j))
                | j <- [0 .. m - 1]
                ]
       in (vs ++ [vm], us')
    extract (vs, _) = last vs

-- | Exponential series as a coinductive stream.
expSeries ::
  (ExpField a, FromInteger a) =>
  a ->
  [a] ->
  [a]
expSeries u0 us = exp u0 : CP.scan (expTailProcess u0) us

instance (Subtractive a, Divisive a, ExpField a, FromInteger a) => ExpField (Jet a) where
  exp (Jet []) = Jet []
  exp (Jet (u0 : us)) = Jet (expSeries u0 us)

  log (Jet []) = Jet []
  log (Jet (u0 : us)) =
    let u = Jet (u0 : us)
     in integrate (log u0) (differentiate u / u)

  sqrt (Jet []) = Jet []
  sqrt (Jet (u0 : us)) = Jet (sqrtSeries u0 us)

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
headCoeff (Jet []) = error "Circuit.Diff.Jet.headCoeff: empty jet"
headCoeff (Jet (c : _)) = c
