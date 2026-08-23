{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Scalar Taylor tower as a circuits arrow.
--
-- A value @Taylor n a b@ is a morphism from @a@ to @b@ whose values are
-- truncated Taylor series of order @n@.  The internal representation is
-- structural: scalar wires carry @n+1@ coefficients, unit wires carry @()@,
-- and product wires pair the two shapes.  This makes the cartesian instances
-- straightforward by recursion on the value shape.
--
-- The carrier is intentionally scalar-first: objects are built from 'Double'
-- and @(,)@, and the bimonoid instances are supplied for 'Double' (and the
-- unit).  The 'Traced' instance ties a lazy knot on the value shape, just as
-- the pure @(->)@ trace does; for stable feedback the coefficients resolve
-- order-by-order.
--
-- Scalar primitives ('addT', 'mulT', etc.) are implemented via
-- 'Circuit.Diff.Jet', so they inherit the correct truncated-series recurrences
-- for addition, multiplication, and elementary functions.
module Circuit.Diff.Taylor
  ( -- * Taylor arrow
    Taylor (..),
    TaylorV (..),

    -- * Scalar primitives
    constT,
    addT,
    mulT,
    sinT,
    cosT,
    expT,
    logT,

    -- * Polynomial construction and evaluation
    polyT,
    shiftT,
    evalTaylor,
    evalTaylorDerivs,

    -- * Bridge from 'Diff'
    taylorCoeffsFromDiff,
    approxTaylorFromDiff,
  )
where

import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Diff (Diff, runDiff)
import Circuit.Diff.Jet (Jet (..), constant, variable)
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Proxy (Proxy (..))
import GHC.TypeNats (KnownNat, Nat, natVal, someNatVal)
import NumHask.Algebra.Additive qualified as NA
import NumHask.Algebra.Field (ExpField (..), TrigField (..))
import NumHask.Algebra.Multiplicative qualified as NM
import Prelude hiding (cos, exp, id, log, sin, (.))

-- | Values carried on a Taylor wire.
data TaylorV (n :: Nat) a where
  VT :: TaylorV n ()
  VD :: [Double] -> TaylorV n Double
  VP :: TaylorV n a -> TaylorV n b -> TaylorV n (a, b)

-- | Truncated Taylor series arrow of order @n@.
newtype Taylor (n :: Nat) a b = Taylor
  { runTaylor :: TaylorV n a -> TaylorV n b
  }

-- ---------------------------------------------------------------------------
-- Scalar series helpers (delegated to Jet)
-- ---------------------------------------------------------------------------

addJets :: [Double] -> [Double] -> [Double]
addJets xs ys = coefficients (Jet xs NA.+ Jet ys)

mulJets :: [Double] -> [Double] -> [Double]
mulJets xs ys = coefficients (Jet xs NM.* Jet ys)

zeroJet :: Int -> Jet Double
zeroJet n = constant n 0

-- ---------------------------------------------------------------------------
-- Category structure
-- ---------------------------------------------------------------------------

instance Category (Taylor n) where
  id = Taylor (\x -> x)
  {-# INLINE id #-}

  Taylor g . Taylor f = Taylor (g . f)
  {-# INLINE (.) #-}

-- ---------------------------------------------------------------------------
-- Cartesian structural maps
-- ---------------------------------------------------------------------------

instance Channel (,) (Taylor n) where
  assoc = Taylor $ \case
    VP (VP x y) z -> VP x (VP y z)
  {-# INLINE assoc #-}

  assoc' = Taylor $ \case
    VP x (VP y z) -> VP (VP x y) z
  {-# INLINE assoc' #-}

  slide = Taylor $ \case
    VP x (VP y z) -> VP y (VP x z)
  {-# INLINE slide #-}

instance Strength (,) (Taylor n) where
  strength (Taylor f) = Taylor $ \case
    VP a b -> VP a (f b)
  {-# INLINE strength #-}

instance Tensor (,) (Taylor n) where
  tensor (Taylor f) (Taylor g) = Taylor $ \case
    VP x y -> VP (f x) (g y)
  {-# INLINE tensor #-}

  unitl = Taylor $ \case
    VP VT x -> x
  {-# INLINE unitl #-}

  unitl' = Taylor $ \x -> VP VT x
  {-# INLINE unitl' #-}

  unitr = Taylor $ \case
    VP x VT -> x
  {-# INLINE unitr #-}

  unitr' = Taylor $ \x -> VP x VT
  {-# INLINE unitr' #-}

instance Action (,) (Taylor n) where
  braid = Taylor $ \case
    VP x y -> VP y x
  {-# INLINE braid #-}

-- ---------------------------------------------------------------------------
-- Trace: lazy knot on the value shape
-- ---------------------------------------------------------------------------

instance Traced (,) (Taylor n) where
  trace (Taylor body) = Taylor $ \b ->
    let VP a c = body (VP a b)
     in c
  {-# INLINE trace #-}

-- ---------------------------------------------------------------------------
-- Bimonoid structure for the unit and for scalar 'Double'
-- ---------------------------------------------------------------------------

instance Copy (Taylor n) () where
  copy = Taylor $ \VT -> VP VT VT
  {-# INLINE copy #-}

instance Discard (Taylor n) () where
  discard = Taylor $ \VT -> VT
  {-# INLINE discard #-}

instance Merge (Taylor n) () where
  plus = Taylor $ \(VP VT VT) -> VT
  {-# INLINE plus #-}

instance Zero (Taylor n) () where
  zero = Taylor $ \VT -> VT
  {-# INLINE zero #-}

instance Copy (Taylor n) Double where
  copy = Taylor $ \(VD xs) -> VP (VD xs) (VD xs)
  {-# INLINE copy #-}

instance Discard (Taylor n) Double where
  discard = Taylor $ \_ -> VT
  {-# INLINE discard #-}

instance Merge (Taylor n) Double where
  plus = Taylor $ \(VP (VD xs) (VD ys)) -> VD (addJets xs ys)
  {-# INLINE plus #-}

instance (KnownNat n) => Zero (Taylor n) Double where
  zero = Taylor $ \VT -> VD (replicate (n + 1) 0)
    where
      n = fromIntegral (natVal (Proxy :: Proxy n))
  {-# INLINE zero #-}

-- ---------------------------------------------------------------------------
-- Scalar primitives
-- ---------------------------------------------------------------------------

-- | Constant scalar morphism.
constT :: Double -> Taylor n Double Double
constT c = Taylor $ \(VD xs) -> VD (coefficients (constant (length xs - 1) c))
{-# INLINE constT #-}

-- | Add two scalar series.
addT :: Taylor n (Double, Double) Double
addT = Taylor $ \(VP (VD xs) (VD ys)) -> VD (addJets xs ys)
{-# INLINE addT #-}

-- | Multiply two scalar series.
mulT :: Taylor n (Double, Double) Double
mulT = Taylor $ \(VP (VD xs) (VD ys)) -> VD (mulJets xs ys)
{-# INLINE mulT #-}

-- | Sine of a scalar series.
sinT :: Taylor n Double Double
sinT = Taylor $ \(VD xs) -> VD (coefficients (sin (Jet xs)))
{-# INLINE sinT #-}

-- | Cosine of a scalar series.
cosT :: Taylor n Double Double
cosT = Taylor $ \(VD xs) -> VD (coefficients (cos (Jet xs)))
{-# INLINE cosT #-}

-- | Exponential of a scalar series.
expT :: Taylor n Double Double
expT = Taylor $ \(VD xs) -> VD (coefficients (exp (Jet xs)))
{-# INLINE expT #-}

-- | Logarithm of a scalar series.
logT :: Taylor n Double Double
logT = Taylor $ \(VD xs) -> VD (coefficients (log (Jet xs)))
{-# INLINE logT #-}

-- ---------------------------------------------------------------------------
-- Polynomial construction and evaluation
-- ---------------------------------------------------------------------------

-- | Build a polynomial morphism from coefficients @[c0, c1, ..., ck]@,
-- mapping the input series @u@ to @c0 + c1*u + c2*u^2 + ... + ck*u^k@.
polyT :: [Double] -> Taylor n Double Double
polyT cs = Taylor $ \(VD xs) ->
  let n = length xs - 1
      x = Jet xs
      go c acc = constant n c NA.+ x NM.* acc
   in VD (coefficients (foldr go (zeroJet n) cs))
{-# INLINE polyT #-}

-- | Shift the input series by a constant @x0@.
shiftT :: Double -> Taylor n Double Double
shiftT x0 = Taylor $ \(VD xs) ->
  let n = length xs - 1
   in VD (addJets xs (coefficients (constant n x0)))
{-# INLINE shiftT #-}

-- | Evaluate a scalar Taylor morphism at a point and return the Taylor
-- coefficients @[f(x), f'(x), f''(x)/2!, ...]@.
evalTaylor :: forall n. (KnownNat n) => Taylor n Double Double -> Double -> [Double]
evalTaylor t x = case runTaylor t (VD seed) of
  VD ys -> ys
  where
    seed = case natVal (Proxy :: Proxy n) of
      0 -> [x]
      m -> x : 1 : replicate (fromIntegral m - 1) 0
{-# INLINE evalTaylor #-}

-- | Evaluate a scalar Taylor morphism and return the raw derivatives
-- @[f(x), f'(x), f''(x), ..., f^(n)(x)]@.
evalTaylorDerivs :: forall n. (KnownNat n) => Taylor n Double Double -> Double -> [Double]
evalTaylorDerivs t x =
  let cs = evalTaylor t x
      facts = scanl (*) 1.0 [1.0 .. fromIntegral n]
   in zipWith (*) cs facts
  where
    n :: Int
    n = fromIntegral (natVal (Proxy :: Proxy n))
{-# INLINE evalTaylorDerivs #-}

-- ---------------------------------------------------------------------------
-- Bridge from a 'Diff' scalar function
-- ---------------------------------------------------------------------------

-- | Approximate Taylor coefficients of a 'Diff' scalar function at a point
-- using forward differences.
--
-- The returned list @[c0, c1, ..., ck]@ represents
-- @f(x0 + eps) = c0 + c1*eps + c2*eps^2 + ... + ck*eps^k@.
taylorCoeffsFromDiff :: Diff p Double Double -> Double -> Int -> [Double]
taylorCoeffsFromDiff f x0 k =
  let h = 1e-4 * max 1.0 (abs x0)
      samples = [fst (runDiff f (x0 + fromIntegral j * h)) | j <- [0 .. k]]
      fwdDiffs = iterate (\ds -> zipWith (-) (drop 1 ds) ds) samples
      c i = (fwdDiffs !! i) !! 0 / (factD i * h ^ i)
   in [c i | i <- [0 .. k]]
  where
    factD 0 = 1.0
    factD n' = fromIntegral (product [1 .. n' :: Int] :: Int)

-- | Build a 'Taylor' morphism that approximates a 'Diff' scalar function
-- near @x0@.
approxTaylorFromDiff ::
  forall n p.
  (KnownNat n) =>
  Diff p Double Double ->
  Double ->
  Taylor n Double Double
approxTaylorFromDiff f x0 =
  let cs = take (n + 1) (taylorCoeffsFromDiff f x0 n)
   in polyT cs . shiftT x0
  where
    n = fromIntegral (natVal (Proxy :: Proxy n))
