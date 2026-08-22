{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Linear cotangent maps — the base arrow for reverse-mode gradients.
--
-- @Pullback b a@ is a linear map @b -> a@ read as an arrow from @b@
-- (output cotangent) to @a@ (input cotangent).  Composition is plain
-- function composition — the /reversal/ is not in this category, it is
-- in how nets are built over it: 'Circuit.Diff.Backprop.linearizeAt' transposes a
-- @Net (,) (Diff p) a b@ into a @Net (,) Pullback b a@, emitting
-- @Compose f' g'@ for every source @Compose g f@.  Within an arrow the
-- chain rule is then just @(.)@.
--
-- This is the arrow that 'linearizeAt' builds: a 'Net' whose wires
-- carry pullbacks rather than smooth maps.  It is the honest linear
-- semantics behind reverse-mode AD, free of the second-derivative
-- confusion that comes from trying to compose 'Diff arrows directly.
module Circuit.Diff.Pullback
  ( -- * Linear cotangent arrow
    Pullback (..),

    -- * Running a pullback net
    evalPullback,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Layer (run)
import Circuit.Net (Net)
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Bifunctor
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Category (Category (..))
-- >>> import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), Zero (..))
-- >>> import Circuit.Channel (Channel (..), Strength (..), Traced (..))
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Circuit.Net (Net (..))
-- >>> import Prelude hiding (id, (.))

-- | A linear map from output cotangents to input cotangents, read as
-- an arrow @b -> a@.
--
-- >>> let pb = Pullback (*2) :: Pullback Double Double
-- >>> runPullback pb 3
-- 6.0
newtype Pullback b a = Pullback
  { -- | Apply the pullback to an output cotangent.
    runPullback :: b -> a
  }

instance Category Pullback where
  id = Pullback id
  Pullback g . Pullback f = Pullback (\x -> g (f x))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

-- | Parallel composition pairs pullbacks independently; 'braid' swaps
-- the two cotangents.
--
-- >>> let f = Pullback (+1) :: Pullback Int Int
-- >>> let g = Pullback (*2) :: Pullback Int Int
-- >>> runPullback (tensor f g) (3, 4)
-- (4,8)
instance Tensor (,) Pullback where
  tensor (Pullback f) (Pullback g) = Pullback (Data.Bifunctor.bimap f g)
  {-# INLINE tensor #-}
  unitl = Pullback snd
  {-# INLINE unitl #-}
  unitl' = Pullback ((),)
  {-# INLINE unitl' #-}
  unitr = Pullback fst
  {-# INLINE unitr #-}
  unitr' = Pullback (,())
  {-# INLINE unitr' #-}

instance Action (,) Pullback where
  braid = Pullback (\(b, a) -> (a, b))
  {-# INLINE braid #-}

instance Strength (,) Pullback where
  strength (Pullback f) = Pullback (\(a, b) -> (a, f b))
  {-# INLINE strength #-}

-- | The cartesian trace for pullbacks.
--
-- The body is a linear map @f :: (x, c) -> (x, b)@.  The traced
-- pullback @c -> b@ solves the affine feedback equation in cotangent
-- space:
--
-- > (dx, db) = f (dx, dc)
--
-- solved by the same lazy knot that 'Trace Diff (,)' uses.  For
-- strict carriers with nonzero channel self-coupling this diverges,
-- exactly as the lazy 'Diff trace does.  Unlike the 'Diff case,
-- though, the equation here is /always affine/ — 'Pullback' arrows are
-- linear by construction — so a knot over a star-semiring carrier can
-- be eliminated outright ('NumHask' @star@ \/
-- 'Circuit.Mat.Dense.starMatrix') rather than iterated.  See
-- @Circuit.Diff.Star@ for the closed forms.
--
-- >>> let body = Pullback (\(dx', dc) -> (2.0 * dc, dx')) :: Pullback (Double, Double) (Double, Double)
-- >>> runPullback (trace body) 1.0
-- 2.0
instance Traced (,) Pullback where
  trace (Pullback f) = Pullback $ \dc ->
    let ~(dx, db) = f (dx, dc)
     in db
  {-# INLINE trace #-}

-- | Pullback-instance of the comonoid structure.
--
-- Copy's pullback is addition; discard's pullback is the zero
-- cotangent.  These are not used by 'linearizeAt' (which encodes
-- structural rows as 'Lift's to avoid channel-type constraints), but
-- they make 'Pullback' a full bimonoid carrier.
--
-- >>> runPullback (copy :: Pullback Int (Int, Int)) 3
-- (3,3)
-- >>> runPullback (discard :: Pullback Int ()) 5
-- ()
--
-- NOTE: unlike @Dup Diff@ (whose pullback genuinely needs 'plus'),
-- neither method here uses the @Additive (->) a@ constraint — copying
-- and discarding are linear as they stand.  If the 'Dup' class head
-- permits, drop the constraint; keeping a stray @Additive@ here reads
-- as \"addition happens in this instance\", which is exactly the
-- confusion the paragraph above tries to dispel.
instance Copy Pullback a where
  copy = Pullback (\b -> (b, b))
  {-# INLINE copy #-}

instance Discard Pullback a where
  discard = Pullback (const ())
  {-# INLINE discard #-}

-- | Pullback-instance of the additive/monoid structure.
--
-- Addition's pullback is copying; zero's pullback is discarding.
--
-- >>> runPullback (plus :: Pullback (Int, Int) Int) (1, 2)
-- 3
-- >>> runPullback (zero :: Pullback () Int) ()
-- 0
instance (Merge (->) a) => Merge Pullback a where
  plus = Pullback (\(b1, b2) -> plus (b1, b2))
  {-# INLINE plus #-}

instance (Zero (->) a) => Zero Pullback a where
  zero = Pullback (\() -> zero ())
  {-# INLINE zero #-}

-- | Evaluate a pullback net at a single output cotangent.
--
-- This is the one-shot reverse pass: the net was built by
-- 'linearizeAt', and applying it to a cotangent @db@ yields the
-- input cotangent @da@.
evalPullback :: Net (,) Pullback b a -> b -> a
evalPullback n = runPullback (run n)
{-# INLINE evalPullback #-}

-- | Cartesian channel plumbing for pullbacks.
instance Channel (,) Pullback where
  assoc = Pullback (\((s, s'), x) -> (s, (s', x)))
  assoc' = Pullback (\(s, (s', x)) -> ((s, s'), x))
  slide = Pullback (\(s, (s', x)) -> (s', (s, x)))
