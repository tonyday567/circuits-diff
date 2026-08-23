{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Parameterised reverse-mode automatic differentiation.
--
-- 'DiffP' is a differentiable operation with parameters @p@, input @a@ and
-- output @b@.  Running forward produces the output; the backward pass, given
-- a cotangent on the output, produces the input cotangent and parameter
-- gradients.
--
-- This is the same shape as 'Circuit.Diff.Diff' from @circuits-ad@, but with
-- an explicit parameter carrier @p@.  When @p = ()@ and the parameter
-- gradient is discarded, 'DiffP' reduces to 'Diff' (see 'toParam' and
-- 'fromParam').
--
-- The representation is the denotation @p -> a -> (b, b -> (a, p))@ rather
-- than a pair of separate forward/backward fields, so it stays aligned with
-- the monomial/lens reading of AD.
module Circuit.Diff.Param
  ( -- * Parameterised differentiable arrow
    DiffP (..),

    -- * Primitive contract
    TensorPrim (..),
    fromPrim,
    toPrim,

    -- * Wiring helpers
    residual,
    splitP,
    joinP,

    -- * Relationship to the phantom-tagged Diff arrow
    toParam,
    fromParam,
  )
where

import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), MergeZero, Zero (..))
import Circuit.Bimonoid qualified as CB
import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..))
import Circuit.Diff (Diff (..), runDiff)
import Circuit.Tensor (Action (..), Tensor (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Diff.Param
-- >>> import Circuit.Category (Category (..))
-- >>> import Circuit.Bimonoid (Copy (..), Discard (..), Merge (..), MergeZero, Zero (..))
-- >>> import Circuit.Tensor (Action (..), Tensor (..))
-- >>> import Circuit.Diff (Diff (..), Diff', runDiff)
-- >>> import Prelude hiding (id, (.))

----------------------------------------------------------------------
-- Core type
----------------------------------------------------------------------

-- | A differentiable operation with parameters @p@, input @a@ and output @b@.
--
-- The forward pass closes over the parameter @p@ and input @a@, producing an
-- output @b@ and a pullback.  The pullback maps an output cotangent @db@ to
-- an input cotangent @da@ and a parameter gradient @dp@.
--
-- This is a point-dependent lens: the parameter is part of the position,
-- not an extra layer.
newtype DiffP p a b = DiffP
  { runDiffP :: p -> a -> (b, b -> (a, p))
  }

-- | A primitive contract with separate forward and backward fields, easier
-- to read and write for dense linear-algebra primitives.
data TensorPrim p a b = TensorPrim
  { primForward :: p -> a -> b,
    primBackward :: p -> a -> b -> (a, p)
  }

-- | Convert a 'TensorPrim' into a 'DiffP'.
fromPrim :: TensorPrim p a b -> DiffP p a b
fromPrim (TensorPrim f b) = DiffP $ \p a -> (f p a, b p a)
{-# INLINE fromPrim #-}

-- | Convert a 'DiffP' into a 'TensorPrim'.
toPrim :: DiffP p a b -> TensorPrim p a b
toPrim (DiffP f) = TensorPrim (\p a -> fst (f p a)) (\p a db -> snd (f p a) db)
{-# INLINE toPrim #-}

----------------------------------------------------------------------
-- Category
----------------------------------------------------------------------

-- | Sequential composition threads the same parameter @p@ through both
-- arrows and combines the parameter gradients with the monoid structure on
-- @p@.
--
-- Identity returns a zero parameter gradient.  This instance needs
-- @MergeZero (->) p@ because the parameter type must supply both @zero@ (for
-- 'id') and @plus@ (for composing gradients).
--
-- >>> let inc = DiffP (\() x -> (x + 1, \dy -> (dy, ()))) :: DiffP () Int Int
-- >>> let dbl = DiffP (\() x -> (2 * x, \dy -> (2 * dy, ()))) :: DiffP () Int Int
-- >>> let (y, pb) = runDiffP (dbl . inc) () 3
-- >>> y
-- 8
-- >>> pb 1
-- (2,())
--
-- Parameter gradients from both composed arrows accumulate (not just the
-- outer one).  @addParam@ contributes @dpG = dy@; @dblParam@ contributes
-- @dpF = dc@; composition must sum them via 'CB.plus'.
--
-- >>> let addParam = DiffP (\p x -> (x + p, \dy -> (dy, dy))) :: DiffP Int Int Int
-- >>> let dblParam = DiffP (\p b -> (2 * b, \dc -> (2 * dc, dc))) :: DiffP Int Int Int
-- >>> let (y, pb) = runDiffP (dblParam . addParam) 10 3
-- >>> y
-- 26
-- >>> pb 1
-- (2,3)
instance (MergeZero (->) p) => Category (DiffP p) where
  id = DiffP $ \_ a -> (a, (,CB.zero ()))
  {-# INLINE id #-}

  DiffP f . DiffP g = DiffP $ \p a ->
    let (b, gBack) = g p a
        (c, fBack) = f p b
     in ( c,
          \dc ->
            let (db, dpF) = fBack dc
                (da, dpG) = gBack db
             in (da, CB.plus (dpF, dpG))
        )
  {-# INLINE (.) #-}

----------------------------------------------------------------------
-- Monoidal structure on objects
----------------------------------------------------------------------

-- | Structural associator for nested pairs.  No parameters are touched.
--
-- The superclass 'Category (DiffP p)' requires 'MergeZero (->) p', so the
-- instance carries the same constraint even though the structural maps
-- themselves ignore the parameter.
instance (MergeZero (->) p) => Channel (,) (DiffP p) where
  assoc = DiffP $ \_ ((a, b), c) -> ((a, (b, c)), \(da, (db, dc)) -> (((da, db), dc), CB.zero ()))
  {-# INLINE assoc #-}

  assoc' = DiffP $ \_ (a, (b, c)) -> (((a, b), c), \((da, db), dc) -> ((da, (db, dc)), CB.zero ()))
  {-# INLINE assoc' #-}

  slide = DiffP $ \_ (a, (b, c)) -> ((b, (a, c)), \(db, (da, dc)) -> ((da, (db, dc)), CB.zero ()))
  {-# INLINE slide #-}

----------------------------------------------------------------------
-- Monoidal product of morphisms
----------------------------------------------------------------------

-- | Parallel composition runs both arrows with the same parameter @p@ and
-- combines their parameter gradients.
--
-- The parameter is treated as an input value, not a state, so it can be
-- passed to both branches without a comonoid structure.  Only the output
-- gradients need @plus@.
--
-- >>> let inc = DiffP (\() x -> (x + 1, \dy -> (dy, ()))) :: DiffP () Int Int
-- >>> let dbl = DiffP (\() x -> (2 * x, \dy -> (2 * dy, ()))) :: DiffP () Int Int
-- >>> let (y, pb) = runDiffP (tensor inc dbl) () (3, 4)
-- >>> y
-- (4,8)
-- >>> pb (1, 1)
-- ((1,2),())
instance (MergeZero (->) p) => Tensor (,) (DiffP p) where
  tensor (DiffP f) (DiffP g) = DiffP $ \p (a, c) ->
    let (b, fBack) = f p a
        (d, gBack) = g p c
     in ( (b, d),
          \(db, dd) ->
            let (da, dpF) = fBack db
                (dc, dpG) = gBack dd
             in ((da, dc), CB.plus (dpF, dpG))
        )
  {-# INLINE tensor #-}
  unitl = DiffP $ \_ ((), a) -> (a, \da -> (((), da), CB.zero ()))
  {-# INLINE unitl #-}
  unitl' = DiffP $ \_ a -> (((), a), \((), da) -> (da, CB.zero ()))
  {-# INLINE unitl' #-}
  unitr = DiffP $ \_ (a, ()) -> (a, \da -> ((da, ()), CB.zero ()))
  {-# INLINE unitr #-}
  unitr' = DiffP $ \_ a -> ((a, ()), \(da, ()) -> (da, CB.zero ()))
  {-# INLINE unitr' #-}

instance (MergeZero (->) p) => Action (,) (DiffP p) where
  braid = DiffP $ \_ (a, b) -> ((b, a), \(db, da) -> ((da, db), CB.zero ()))
  {-# INLINE braid #-}

----------------------------------------------------------------------
-- Bimonoid structure
----------------------------------------------------------------------

-- | Copy in 'DiffP': forward copy, backward add.  The parameter gradient is
-- zero because copy has no parameters.
--
-- >>> let (_, pb) = runDiffP copy () (5 :: Int)
-- >>> pb (1, 2)
-- (3,())
instance (Merge (->) a, Zero (->) p) => Copy (DiffP p) a where
  copy = DiffP $ \_ a -> ((a, a), \(da1, da2) -> (CB.plus (da1, da2), CB.zero ()))
  {-# INLINE copy #-}

instance (Zero (->) a, Zero (->) p) => Discard (DiffP p) a where
  discard = DiffP $ \_ _ -> ((), const (CB.zero (), CB.zero ()))
  {-# INLINE discard #-}

-- | Add in 'DiffP': forward add, backward copy.  The parameter gradient is
-- zero because addition has no parameters.
--
-- >>> let (_, pb) = runDiffP plus () ((3, 4) :: (Int, Int))
-- >>> pb 1
-- ((1,1),())
instance (Merge (->) a, Zero (->) p) => Merge (DiffP p) a where
  plus = DiffP $ \_ (a, b) -> (CB.plus (a, b), \d -> ((d, d), CB.zero ()))
  {-# INLINE plus #-}

instance (Zero (->) a, Zero (->) p) => Zero (DiffP p) a where
  zero = DiffP $ \_ () -> (CB.zero (), const ((), CB.zero ()))
  {-# INLINE zero #-}

----------------------------------------------------------------------
-- Wiring helpers
----------------------------------------------------------------------

-- | Add a residual connection around an operation.
--
--   forward:  y = x + op(x)
--   backward: dx = dy + dOp
residual :: (Num a) => DiffP p a a -> DiffP p a a
residual op = DiffP $ \p a ->
  let (b, opBack) = runDiffP op p a
   in ( a + b,
        \dy ->
          let (daOp, dp) = opBack dy
           in (dy + daOp, dp)
      )
{-# INLINE residual #-}

-- | Split a parameter tuple so the left and right halves can be used by
-- independent parallel branches.
--
-- This is the parameter-product combinator that the fixed-parameter
-- 'Category' instance cannot express.  It keeps the migration semantics
-- identical to the original circuits-llm 'DiffP'.
splitP :: DiffP p1 a1 b1 -> DiffP p2 a2 b2 -> DiffP (p1, p2) (a1, a2) (b1, b2)
splitP (DiffP f1) (DiffP f2) = DiffP $ \(p1, p2) (a1, a2) ->
  let (b1, back1) = f1 p1 a1
      (b2, back2) = f2 p2 a2
   in ( (b1, b2),
        \(db1, db2) ->
          let (da1, dp1) = back1 db1
              (da2, dp2) = back2 db2
           in ((da1, da2), (dp1, dp2))
      )
{-# INLINE splitP #-}

-- | Pair two operations that share the same input type but produce
-- independent outputs.  Input cotangents are added; parameter gradients are
-- paired.
joinP :: (Num a) => DiffP p1 a b1 -> DiffP p2 a b2 -> DiffP (p1, p2) a (b1, b2)
joinP (DiffP f1) (DiffP f2) = DiffP $ \(p1, p2) a ->
  let (b1, back1) = f1 p1 a
      (b2, back2) = f2 p2 a
   in ( (b1, b2),
        \(db1, db2) ->
          let (da1, dp1) = back1 db1
              (da2, dp2) = back2 db2
           in (da1 + da2, (dp1, dp2))
      )
{-# INLINE joinP #-}

----------------------------------------------------------------------
-- Relationship to the phantom-tagged Diff arrow
----------------------------------------------------------------------

-- | Embed a phantom-tagged 'Diff' into 'DiffP ()'.  The phantom tag is
-- discarded because 'DiffP' carries parameters at the value level.
--
-- >>> let d = Diff (\x -> (x * x, \dy -> 2 * x * dy)) :: Diff () Double Double
-- >>> let (y, pb) = runDiffP (toParam d) () 3.0
-- >>> y
-- 9.0
-- >>> pb 1.0
-- (6.0,())
toParam :: Diff q a b -> DiffP () a b
toParam d = DiffP $ \_ a ->
  let (b, pb) = runDiff d a
   in (b, \db -> (pb db, ()))
{-# INLINE toParam #-}

-- | Project a parameter-free 'DiffP ()' back into the phantom-tagged
-- 'Diff' arrow.
--
-- This is a section/retract pair with 'toParam':
-- @fromParam . toParam = id@ for the parameter-free fragment.
--
-- >>> let d = Diff (\x -> (x * x, \dy -> 2 * x * dy)) :: Diff () Double Double
-- >>> let (y, pb) = runDiff (fromParam (toParam d)) 3.0
-- >>> y
-- 9.0
-- >>> pb 1.0
-- 6.0
fromParam :: DiffP () a b -> Diff () a b
fromParam (DiffP f) = Diff $ \a ->
  let (b, pb) = f () a
   in (b, fst . pb)
{-# INLINE fromParam #-}
