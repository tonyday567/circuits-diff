{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- | 'Diff'' as a circuits arrow.
--
-- This module gives the instances that turn the differentiable carrier
-- 'Circuit.Diff.Diff'' into a 'Circuit.Category.Category' with tracing,
-- channels, strength, tensor products, and bimonoid structure.  Keeping the
-- instances in the same package as the 'Diff'' type avoids the orphan
-- instances that would arise if 'circuits-ad' defined them for a carrier
-- living elsewhere.
module Circuit.Diff.Circuit
  ( -- * Re-exports from the carrier
    Diff,
    Diff',
    pattern Diff,
    runDiff,

    -- * Traced variants
    traceNFrom,
    traceStarFrom,
    traceStar,

    -- * Smoke test
    quadD,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..), Traced (..))
import Circuit.Dagger (Copy (..), Discard (..), Merge (..), MergeZero, Zero (..))
import Circuit.Dagger qualified as CD
import Circuit.Diff (Diff, Diff', runDiff, pattern Diff)
import Circuit.Tensor (Action (..), Tensor (..))
import Data.Bifunctor
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit.Dagger (Copy (..), Merge (..))
-- >>> import Circuit.Tensor (Action (..), Tensor (..))

-- | 'Circuit.Category.Category' for 'Diff''.
--
-- 'Circuit.Diff' still provides 'Control.Category'; circuits needs the local
-- 'Category' with associated 'Ob' (default @()@) so 'Monoidal' / 'Traced' /
-- free 'Trace' folds typecheck after kind-gen.
instance Category (Diff' p) where
  id = Diff (\a -> (a, id))
  Diff f . Diff g = Diff $ \a ->
    let (b, gb) = g a
        (c, fc) = f b
     in (c, \dc -> gb (fc dc))
  {-# INLINE id #-}
  {-# INLINE (.) #-}

-- | 'Trace' for 'Diff' with the @(,)@ tensor.
--
-- The forward pass ties the standard lazy knot:
--
-- @
-- let (a, c) = body (a, b) in c
-- @
--
-- The backward pass ties the /same shape/ of knot, transposed.  Given @dc@
-- on the output, the full backward pair @(da, db)@ satisfies a self-referential
-- equation solved by a single lazy binding:
--
-- @
-- let bd = backward (fst bd, dc) in snd bd
-- @
--
-- The knot flows through the /pair/ rather than through the channel cotangent
-- alone — 'backward' is called once, the pair is destructured once, and the
-- shape mirrors the forward knot identically.
--
-- 'pullback' closes over 'backward', which closes over the forward pass's
-- intermediates.  The closure is the tape: no explicit Wengert list is built
-- because GHC's heap holds the graph.  For linear backward maps this is a
-- Neumann series computed lazily; for general maps it is the implicit function
-- theorem as a lazy knot.
instance Traced (,) (Diff' p) where
  trace (Diff body) = Diff $ \b ->
    let -- Forward: standard lazy knot
        ~((a, c), backward) = body (a, b)
        -- Backward: same shape, transposed — knot through the pair
        pullback dc =
          let bd = backward (fst bd, dc)
           in snd bd
     in (c, pullback)

-- | Cartesian channel plumbing for 'Diff'.
instance Channel (,) (Diff' p) where
  assoc = Diff (\((s, s'), x) -> ((s, (s', x)), \(s'', (s''', x')) -> ((s'', s'''), x')))
  assoc' = Diff (\(s, (s', x)) -> (((s, s'), x), \((s'', s'''), x') -> (s'', (s''', x'))))
  slide = Diff (\(s, (s', x)) -> ((s', (s, x)), \(s'', (s''', x')) -> (s''', (s'', x'))))

-- | Cocartesian channel plumbing for 'Diff'.
instance Channel Either (Diff' p) where
  assoc =
    Diff
      ( \case
          Left (Left a) -> (Left a, \case Left da -> Left (Left da); Right _ -> error "assoc")
          Left (Right b) -> (Right (Left b), \case Right (Left db) -> Left (Right db); _ -> error "assoc")
          Right c -> (Right (Right c), \case Right (Right dc) -> Right dc; _ -> error "assoc")
      )
  assoc' =
    Diff
      ( \case
          Left a -> (Left (Left a), \case Left (Left da) -> Left da; _ -> error "assoc'")
          Right (Left b) -> (Left (Right b), \case Left (Right db) -> Right (Left db); _ -> error "assoc'")
          Right (Right c) -> (Right c, \case Right dc -> Right (Right dc); _ -> error "assoc'")
      )
  slide =
    Diff
      ( \case
          Left a -> (Right (Left a), \case Right (Left da) -> Left da; _ -> error "slide")
          Right (Left b) -> (Left b, \case Left db -> Right (Left db); _ -> error "slide")
          Right (Right c) -> (Right (Right c), \case Right (Right dc) -> Right (Right dc); _ -> error "slide")
      )

-- | Cartesian tensorial strength for 'Diff'.
instance Strength (,) (Diff' p) where
  strength (Diff f) = Diff $ \(a, b) ->
    let (c, back) = f b
     in ((a, c), \(da, dc) -> (da, back dc))
  {-# INLINE strength #-}

-- | Cocartesian tensorial strength for 'Diff'.
instance Strength Either (Diff' p) where
  strength (Diff f) = Diff $ \case
    Left a -> (Left a, \case Left da -> Left da; Right _ -> error "strength: Left input, Right cotangent")
    Right b ->
      let (c, back) = f b
       in (Right c, \case Right dc -> Right (back dc); Left _ -> error "strength: Right input, Left cotangent")
  {-# INLINE strength #-}

-- | Trace for 'Diff' with the 'Either' tensor.
--
-- The 'Either' trace is a while-loop: 'Left a' means "iterate again",
-- 'Right c' means "return".  Forward pass runs until the body produces a
-- 'Right', recording each body's pullback.  Backward pass replays those
-- pullbacks in reverse order, propagating the output cotangent back through
-- the iteration chain.
--
-- The number of iterations is treated as locally constant by the derivative:
-- small perturbations of the input do not change the branch sequence.  This
-- is the standard reverse-mode treatment of data-dependent control flow.
--
-- __Proof obligation__ (joins the linearity obligation on the other
-- traces): a cotangent on a sum is represented as the /same/ sum, and
-- its tag must match the primal trajectory — the cotangent space at a
-- point of @Either a c@ is the cotangent space of the branch the point
-- is in.  Every honest pullback maps an output-tagged cotangent to an
-- input-tagged one; the replay errors loudly on any mismatch rather
-- than misreading a dishonest primitive.
instance Traced Either (Diff' p) where
  trace (Diff body) = Diff $ \b ->
    let -- Forward: iterate, collecting pullbacks in execution order.
        goFwd x =
          let (y, pb) = body x
           in case y of
                Right c' -> (c', [pb])
                Left a ->
                  let (c', pbs') = goFwd (Left a)
                   in (c', pb : pbs')
        (c, pbs) = goFwd (Right b)
        -- Reverse the tape once; shared across all cotangents.
        rpbs = reverse pbs
        -- Backward: replay pullbacks in reverse order.
        pullback dc =
          case rpbs of
            [] -> error "Circuit.Diff.Circuit.Trace Diff Either: empty loop (impossible)"
            (lastPb : prevPbs) -> goBwd (lastPb (Right dc)) prevPbs
          where
            goBwd (Right db) [] = db
            goBwd (Left _) [] =
              error "Circuit.Diff.Circuit.Trace Diff Either: final cotangent landed on Left (impossible)"
            goBwd (Left da) (pb : pbs') = goBwd (pb (Left da)) pbs'
            goBwd (Right _) (_ : _) =
              -- A Right-tagged cotangent with pullbacks still pending means
              -- some pullback at iteration i > 1 claimed its input was the
              -- exit branch — but that iteration's primal input was 'Left'.
              -- Returning here would silently skip the remaining chain rule,
              -- so this is a dishonest primitive, not an early exit.
              error "Circuit.Diff.Circuit.Trace Diff Either: Right cotangent mid-chain (tag-dishonest pullback)"
     in (c, pullback)

-- ---------------------------------------------------------------------------
-- Copy / Discard / Merge / Zero for Diff — the bimonoid structure of the
-- differentiable arrow.
--
-- In Diff, the bimonoid is self-dual under differentiation: copy's pullback
-- is plus, discard's pullback is zero, plus's pullback is copy, zero's
-- pullback is discard.  transpose's Copy ↔ Add, Discard ↔ Zero table is
-- not a rule imposed on syntax — it's the instance structure of Diff read
-- off at the semantic level.

-- | Copy in D: the pullback is 'plus' (fan-in on the backward pass).
--
-- >>> import Circuit.Tensor (Action(..))
-- >>> import Circuit.Dagger (Copy(..), Merge(..))
-- >>> let (_, pb) = runDiff (copy :: Diff Int (Int, Int)) 5
-- >>> pb (1, 2)
-- 3
instance (Merge (->) a) => Copy (Diff' p) a where
  copy = Diff (\a -> ((a, a), CD.plus))
  {-# INLINE copy #-}

instance (Zero (->) a) => Discard (Diff' p) a where
  discard = Diff (const ((), \() -> CD.zero ()))
  {-# INLINE discard #-}

-- | Add in D: the pullback is 'copy' (fan-out on the backward pass).
--
-- >>> let (_, pb) = runDiff (plus :: Diff (Int, Int) Int) (3, 4)
-- >>> pb 1
-- (1,1)
instance (Merge (->) a) => Merge (Diff' p) a where
  plus = Diff (\(a, b) -> (CD.plus (a, b), \d -> (d, d)))
  {-# INLINE plus #-}

instance (Zero (->) a) => Zero (Diff' p) a where
  zero = Diff (\() -> (CD.zero (), const ()))
  {-# INLINE zero #-}

-- | Monoidal product for Diff: independent wires, no additive constraint.
--
-- >>> let f = Diff (\x -> (x + 1, \d -> d)) :: Diff Int Int
-- >>> let g = Diff (\x -> (x * 2, \d -> 2 * d)) :: Diff Int Int
-- >>> let (y, pb) = runDiff (par f g) (3, 4)
-- >>> y
-- (4,8)
-- >>> pb (1, 1)
-- (1,2)
instance Tensor (,) (Diff' p) where
  par (Diff f) (Diff g) = Diff $ \(a, c) ->
    let (b, fb) = f a; (d, gd) = g c
     in ((b, d), Data.Bifunctor.bimap fb gd)
  {-# INLINE par #-}
  unitl = Diff (\((), a) -> (a, ((),)))
  {-# INLINE unitl #-}
  unitl' = Diff (\a -> (((), a), \((), da) -> da))
  {-# INLINE unitl' #-}
  unitr = Diff (\(a, ()) -> (a, (,())))
  {-# INLINE unitr #-}
  unitr' = Diff (\a -> ((a, ()), \(da, ()) -> da))
  {-# INLINE unitr' #-}

instance Action (,) (Diff' p) where
  swap = Diff (\(a, b) -> ((b, a), \(db, da) -> (da, db)))
  {-# INLINE swap #-}

-- ---------------------------------------------------------------------------
-- StarSemiring — the principled Neumann index
-- ---------------------------------------------------------------------------

-- | Trace with a closed-form backward pass via the Kleene 'NHR.star'.
--
-- The integer @n@ in 'traceNFrom' truncates a series on /both/ passes.
-- But only the forward fixpoint is genuinely nonlinear; the backward
-- channel equation is affine — calculus promises linearity in
-- cotangents:
--
-- > da = A·da + C·dc        solution:  da = star A · C·dc
--
-- with @star a = one + a·star a@ — the Neumann series as algebra,
-- @1\/(1−a)@ over a field.  Because the pullback is linear, the
-- blocks A and C·dc are /extractable by probing/:
--
-- > backward (dj, dc) = (A·dj + C·dc, B·dj + D·dc)
-- > A    = fst (backward (one,  0))   -- channel self-coupling
-- > C·dc = fst (backward (zero, dc))
--
-- and the trace's pullback is the Schur complement
-- @D·dc + B·star A·C·dc@, recovered with one more probe at the
-- backward fixpoint:
--
-- > db = snd (backward (star A · C·dc, dc))
--
-- (Check: @A·(star A·C·dc) + C·dc = (A·star A + one)·C·dc
-- = star A·C·dc@ — the star law discharges the fixpoint.)
--
-- So: forward still iterates from the caller's seed (no closed form
-- exists for an arbitrary nonlinear fixpoint), but the backward pass
-- is /exact/ in three calls to @backward@ — no Neumann index at all.
-- The @star@ probe is computed once per forward point and shared
-- across all cotangents.
--
-- The closed form is the truncated iteration's limit; pure-Prelude
-- witness at @a = 0.3@, @c = 2@:
--
-- >>> let daIter = iterate (\d -> 0.3 * d + 2.0 * 1.0) 0 !! 200
-- >>> abs (daIter - 1.0 / (1.0 - 0.3) * 2.0) < 1e-12
-- True
--
-- __Caveat__: @numhask@ declares 'NHR.StarSemiring' but ships no
-- instances; the only carriers in the tower are
-- 'NumHask.Free.Carriers.FieldStar' (@star a = recip (1−a)@),
-- @Warshall@, and @MinPlus@.  For bare 'Double' channels and for /vector/
-- channels solved by 'Circuit.Mat.Dense.starMatrix', see
-- @Circuit.Diff.Star@ — the Schur-complement bridge proper.
--
-- __Proof obligation__: the probes assume the pullback is linear.
-- Every honestly-constructed 'Diff' primitive satisfies this (a
-- pullback /is/ a linear map); a primitive whose backward closure is
-- affine-with-offset is a bug that this function will silently
-- misread.
traceStarFrom ::
  (NHR.StarSemiring j, MergeZero (->) c) =>
  -- | forward seed
  j ->
  -- | forward iteration count
  Int ->
  Diff' p (j, b) (j, c) ->
  Diff' p b c
traceStarFrom x0 n (Diff body) = Diff $ \b ->
  let -- Forward: iterate from caller-supplied seed (as 'traceNFrom')
      stepFwd x = let ((x', _), _) = body (x, b) in x'
      a = iterate stepFwd x0 !! n
      ((_, c), backward) = body (a, b)
      -- Probe the channel self-coupling once; star it in closed form
      aStar = NHR.star (fst (backward (NHM.one, CD.zero ())))
      -- Backward: exact in two more probes — no iteration
      pullback dc =
        let cdc = fst (backward (NHA.zero, dc))
         in snd (backward (aStar NHM.* cdc, dc))
   in (c, pullback)

-- | Trace via the Kleene star — the execution formula, lazy form.
--
-- For a knot body with channel self-coupling block A and cross-blocks
-- B, C, D, the trace is the Schur complement:
--
-- > traceStar f = D + B · star A · C
--
-- The lazy 'trace' instance for 'Diff' computes exactly this via a
-- lazy fixpoint rather than closed form, so this alias is definable
-- without using 'NHR.star' at all.  Note that @numhask@ ships no
-- 'NHR.StarSemiring' instances, so for concrete carriers prefer
-- 'traceStarFrom' (scalar channel, closed-form backward) or
-- @Circuit.Diff.Star.traceStarMatrix@ (vector channel, solved by
-- 'Circuit.Mat.Dense.starMatrix' — the bridge made literal).
traceStar :: Diff' p (j, b) (j, c) -> Diff' p b c
traceStar = trace

-- | Iterated trace for strict carriers.
--
-- The lazy 'trace' diverges on strict cotangent types ('Double', etc.) when
-- the feedback channel has nonzero self-coupling (@∂a_out\/∂a_in ≠ 0@).
-- 'traceNFrom' replaces the lazy knot with truncated fixed-point iteration.
--
--   * __Forward__ — iterate from caller-supplied seed @x0@, N steps.
--     There is no canonical seed for the forward pass (the fixpoint is
--     arbitrary nonlinear), so the caller provides one.
--
--   * __Backward__ — iterate from 'zero', N steps, extract 'snd' once.
--     The backward equation is guaranteed affine (calculus promises
--     linearity in cotangents), so 'zero' is the principled seed.
--     The Neumann summation happens /inside/ the iteration — no
--     double-counting, and 'plus' retreats to where the theory says
--     it lives: inside prims and 'Copy'.
--
-- Lives beside the lawful-but-lazy instance, not replacing it.
traceNFrom ::
  (MergeZero (->) a) =>
  a ->
  Int ->
  Diff' p (a, b) (a, c) ->
  Diff' p b c
traceNFrom x0 n (Diff body) = Diff $ \b ->
  let -- Forward: iterate from caller-supplied seed
      stepFwd x = let ((x', _), _) = body (x, b) in x'
      a = iterate stepFwd x0 !! n
      ((_, c), backward) = body (a, b)
      -- Backward: iterate from zero, extract result once
      pullback dc =
        let stepBwd d = fst (backward (d, dc))
            da = iterate stepBwd (CD.zero ()) !! n
         in snd (backward (da, dc))
   in (c, pullback)

-- ---------------------------------------------------------------------------
-- Smoke test: quadratic — the term that was impossible in Stage 1
-- ---------------------------------------------------------------------------

-- | @2x² + 3x + 5@ built from 'par', 'dup', and 'plus' on the @Diff@ arrow.
-- No 'Net' needed — the instances are the denotations the rows will realise to.
--
-- The gradient is @4x + 3@, so at @x = 1@: value 10, gradient 7.
--
-- >>> let (y, pb) = runDiff quadD 1.0
-- >>> y
-- 10.0
-- >>> pb 1.0
-- 7.0
quadD :: Diff' p Double Double
quadD = CD.plus . par sq lin . CD.copy
  where
    sq = Diff (\x -> (2 * x * x, \d -> 4 * x * d))
    lin = Diff (\x -> (3 * x + 5, (3 *)))
