{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}

-- | Cartesian reverse differential category structure on 'Diff'.
--
-- A /Cartesian reverse differential category/ (Cockett, Cruttwell, Gallagher,
-- Lemay, MacAdam, Plotkin, Pronk, CSL 2020) is a Cartesian left-additive
-- category with a combinator
--
-- > R[f] : A × B → A
--
-- for every morphism @f : A → B@, satisfying seven coherence axioms [RD.1]–
-- [RD.7].  For 'Diff' the combinator is exactly the bundled pullback:
--
-- > R[f](a, db) = snd (runDiff f a) db
--
-- This module exposes that combinator, the small Cartesian plumbing needed to
-- state the axioms, and value-level checks for all seven axioms.  [RD.6] is
-- homogeneity of @R[f]@ in its cotangent argument; [RD.7] is symmetry of mixed
-- partials (Schwarz), checked via the scalar-line 'Jet' tower.
module Circuit.Diff.RDC
  ( -- * Reverse derivative combinator
    rdc,

    -- * Cartesian helpers on 'Diff'
    fstD,
    sndD,
    pairD,
    forkD,
    terminalD,

    -- * Axiom checks ([RD.1]–[RD.7])
    rdcAdditive,
    rdcLinear,
    rdcHomogeneous,
    rdcIdentity,
    rdcFst,
    rdcSnd,
    rdcPairing,
    rdcTerminal,
    rdcChain,
    rdcMixedPartials,
  )
where

import Circuit.Diff (Diff (..), runDiff)
import Circuit.Diff.Jet (constant, taylor)
import Control.Category
import NumHask.Algebra.Additive (Additive (..))
import NumHask.Algebra.Field (ExpField (..), TrigField (..))
import NumHask.Algebra.Multiplicative (Multiplicative (..))
import NumHask.Data.Integral (FromInteger (..))
import Prelude hiding (fromInteger, id, (*), (+), (.))
import Prelude qualified as P

-- | Reverse derivative combinator.
--
-- For @f : Diff p a b@, the reverse derivative @R[f] : (a, b) -> a@ maps a
-- point @a@ and an output cotangent @db@ to the input cotangent @da@.
--
-- >>> import NumHask.Algebra.Field qualified as NHField
-- >>> import Circuit.Diff
-- >>> let x = Diff (\s -> (s, \db -> db)) :: Diff' Double Double
-- >>> rdc (NHField.sin x) (0.0, 1.0)
-- 1.0
rdc :: Diff p a b -> (a, b) -> a
rdc (Diff f) (a, db) =
  let (_, pullback) = f a
   in pullback db

-- | First projection as a 'Diff' morphism.
fstD :: (Additive b) => Diff p (a, b) a
fstD = Diff $ \(a, _) -> (a, \da -> (da, zero))

-- | Second projection as a 'Diff' morphism.
sndD :: (Additive a) => Diff p (a, b) b
sndD = Diff $ \(_, b) -> (b, \db -> (zero, db))

-- | Pairing of two 'Diff' morphisms with the same source.
pairD ::
  (Additive a) =>
  Diff p a b ->
  Diff p a c ->
  Diff p a (b, c)
pairD (Diff f) (Diff g) = Diff $ \a ->
  let (b, pb) = f a
      (c, pc) = g a
   in ( (b, c),
        \(db, dc) -> pb db + pc dc
      )

-- | Fork a single morphism into a pair: @forkD f = pairD f f@.
forkD ::
  (Additive a) =>
  Diff p a b ->
  Diff p a (b, b)
forkD f = pairD f f

-- | Unique morphism to the terminal object, returning the zero cotangent.
terminalD :: (Additive a) => Diff p a ()
terminalD = Diff $ \_ -> ((), \_ -> zero)

-- | Helper: compare two values up to a tolerance.
near :: (P.Fractional a, P.Ord a) => a -> a -> a -> Bool
near tol x y = P.abs (x P.- y) < tol

-- | [RD.1] The reverse derivative preserves addition: @R[f + g] = R[f] + R[g]@
-- and @R[0] = 0@.
rdcAdditive ::
  (Additive a, Additive b, P.Fractional a, P.Ord a) =>
  a ->
  Diff p a b ->
  Diff p a b ->
  a ->
  b ->
  b ->
  Bool
rdcAdditive tol f g a db1 db2 =
  near
    tol
    (rdc (f + g) (a, db1 + db2))
    (rdc f (a, db1 + db2) + rdc g (a, db1 + db2))
    && near tol (rdc zero (a, db1)) zero

-- | [RD.2] The reverse derivative is additive in its second (cotangent)
-- argument: @R[f](a, db1 + db2) = R[f](a, db1) + R[f](a, db2)@ and
-- @R[f](a, 0) = 0@.
rdcLinear ::
  (Additive a, Additive b, P.Fractional a, P.Ord a) =>
  a ->
  Diff p a b ->
  a ->
  b ->
  b ->
  b ->
  Bool
rdcLinear tol f a db1 db2 db3 =
  near
    tol
    (rdc f (a, db1 + db2 + db3))
    (rdc f (a, db1) + rdc f (a, db2) + rdc f (a, db3))
    && near tol (rdc f (a, zero)) zero

-- | [RD.3] @R[id] = π1@: the reverse derivative of the identity is the
-- second projection (the cotangent itself).
rdcIdentity :: (P.Fractional a, P.Ord a) => a -> a -> a -> Bool
rdcIdentity tol a da = near tol (rdc id (a, da)) da

-- | [RD.3] @R[π0] = ι0 ∘ π1@: the reverse derivative of first projection
-- returns the cotangent in the first component and zero in the second.
rdcFst ::
  (Additive b, P.Fractional a, P.Ord a, P.Eq b) =>
  a ->
  (a, b) ->
  a ->
  Bool
rdcFst tol x da =
  let (da', zeroB) = rdc fstD (x, da)
   in near tol da' da && zeroB == zero

-- | [RD.3] @R[π1] = ι1 ∘ π1@: the reverse derivative of second projection
-- returns zero in the first component and the cotangent in the second.
rdcSnd ::
  (Additive a, P.Fractional a, P.Ord a, P.Eq b) =>
  a ->
  (a, b) ->
  b ->
  Bool
rdcSnd tol x db =
  let (zeroA, db') = rdc sndD (x, db)
   in near tol zeroA zero && db' == db

-- | [RD.4] Reverse derivative of a pairing:
-- @R[<f, g>](a, (db, dc)) = R[f](a, db) + R[g](a, dc)@.
rdcPairing ::
  (Additive a, Additive b, Additive c, P.Fractional a, P.Ord a) =>
  a ->
  Diff p a b ->
  Diff p a c ->
  a ->
  (b, c) ->
  (b, c) ->
  Bool
rdcPairing tol f g a (db1, dc1) (db2, dc2) =
  let lhs = rdc (pairD f g) (a, (db1 + db2, dc1 + dc2))
      rhs = rdc f (a, db1 + db2) + rdc g (a, dc1 + dc2)
   in near tol lhs rhs

-- | [RD.4] Reverse derivative of the terminal morphism is zero.
rdcTerminal ::
  (Additive a, P.Fractional a, P.Ord a) =>
  a ->
  a ->
  Bool
rdcTerminal tol a = near tol (rdc terminalD (a, ())) zero

-- | [RD.5] Reverse chain rule:
-- @R[g ∘ f](a, dc) = R[f](a, R[g](f a, dc))@.
rdcChain ::
  (P.Fractional a, P.Ord a) =>
  a ->
  Diff p a b ->
  Diff p b c ->
  a ->
  c ->
  Bool
rdcChain tol f g a dc =
  let lhs = rdc (g . f) (a, dc)
      rhs = rdc f (a, rdc g (fst (runDiff f a), dc))
   in near tol lhs rhs

-- | [RD.6] The reverse derivative is homogeneous in its cotangent argument:
-- @R[f](a, c · db) = c · R[f](a, db)@.
--
-- This formulation restricts to endomorphisms @f : A → A@ so that the scalar
-- @c@ and the input/output cotangents all live in the same carrier.
rdcHomogeneous ::
  (Multiplicative a, P.Fractional a, P.Ord a) =>
  a ->
  Diff p a a ->
  a ->
  a ->
  a ->
  Bool
rdcHomogeneous tol f a db c =
  near tol (rdc f (a, c * db)) (c * rdc f (a, db))

-- | [RD.7] Symmetry of mixed partials (Schwarz's theorem).
--
-- For a scalar field @f : A × A → A@ we compute the two second-order scalar
-- jets obtained by differentiating first with respect to @x@ and then @y@, and
-- vice-versa, and assert they agree.
--
-- The function argument is rank-2 polymorphic so it can be interpreted both at
-- the base carrier @a@ and at the 'Jet' carrier used for the scalar-line Taylor
-- expansion.
rdcMixedPartials ::
  (ExpField a, TrigField a, FromInteger a, P.Fractional a, P.Ord a) =>
  a ->
  (forall b. (ExpField b, TrigField b, FromInteger b) => (b, b) -> b) ->
  (a, a) ->
  Bool
rdcMixedPartials tol f (x0, y0) =
  let x0J = constant 0 x0
      y0J = constant 0 y0
      dx y = taylor (\x -> f (x, constant 0 y)) 1 x0J !! 1
      dy x = taylor (\y -> f (constant 0 x, y)) 1 y0J !! 1
      dxy = taylor dx 1 y0 !! 1
      dyx = taylor dy 1 x0 !! 1
   in near tol dxy dyx
