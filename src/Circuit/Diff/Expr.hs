-- | A deep embedding of scalar smooth expressions.
--
-- NumHask's free-algebra tower stops at 'Ring' because division has a
-- conditional law (@a / a == one || a == zero@), so it has no initial
-- algebra.  That is a categorical obstacle, not a practical one: we can
-- still write a deep embedding with a 'Recip' constructor and evaluate it
-- into any carrier that already knows how to divide.  The partiality at
-- zero becomes a runtime error in the target carrier, exactly as it is for
-- bare 'Double'.
--
-- This module provides that deep embedding for one scalar variable,
-- including the field and trigonometric operations needed for real AD.
-- Interpretations are provided into 'Double', 'Circuit.Diff.Jet' (exact
-- Taylor towers), and 'Circuit.Diff.Diff' (exact reverse mode).
module Circuit.Diff.Expr
  ( -- * Expression syntax
    Expr (..),

    -- * Interpretation
    evalExpr,
    evalDouble,
    evalJet,

    -- * AD
    derivativeExpr,
    diffExpr,
    taylorExpr,
    derivativeNExpr,
  )
where

import Circuit.Diff (Diff (..))
import Circuit.Diff.Jet (Jet (..), constant, taylor, variable)
import NumHask.Algebra.Additive qualified as NA
import NumHask.Algebra.Field qualified as NF
import NumHask.Algebra.Multiplicative qualified as NM
import Prelude
import Prelude qualified as P

-- | A scalar expression in one variable.
data Expr
  = -- | The input variable.
    Var
  | -- | A numeric literal.
    Lit Double
  | -- | Sum.
    AddE Expr Expr
  | -- | Additive inverse.
    NegE Expr
  | -- | Product.
    MulE Expr Expr
  | -- | Multiplicative inverse (division is @MulE u (RecipE v)@).
    RecipE Expr
  | -- | Exponential.
    ExpE Expr
  | -- | Natural logarithm.
    LogE Expr
  | -- | Sine.
    SinE Expr
  | -- | Cosine.
    CosE Expr
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Overloaded syntax
-- ---------------------------------------------------------------------------

instance Num Expr where
  (+) = AddE
  (*) = MulE
  negate = NegE
  fromInteger = Lit . fromInteger
  abs = P.error "Circuit.Diff.Expr: abs is not differentiable"
  signum = P.error "Circuit.Diff.Expr: signum is not differentiable"

instance Fractional Expr where
  fromRational = Lit . fromRational
  recip = RecipE

instance Floating Expr where
  pi = Lit pi
  exp = ExpE
  log = LogE
  sin = SinE
  cos = CosE
  sinh u = (exp u - exp (-u)) * Lit 0.5
  cosh u = (exp u + exp (-u)) * Lit 0.5
  tanh u = sinh u / cosh u
  asin _ = P.error "Circuit.Diff.Expr: asin is not yet supported"
  acos _ = P.error "Circuit.Diff.Expr: acos is not yet supported"
  atan _ = P.error "Circuit.Diff.Expr: atan is not yet supported"
  asinh _ = P.error "Circuit.Diff.Expr: asinh is not yet supported"
  acosh _ = P.error "Circuit.Diff.Expr: acosh is not yet supported"
  atanh _ = P.error "Circuit.Diff.Expr: atanh is not yet supported"

-- ---------------------------------------------------------------------------
-- Generic evaluation into a NumHask carrier
-- ---------------------------------------------------------------------------

-- | Evaluate an expression at @x@, embedding literals with @lit@.
evalExpr ::
  (NF.ExpField a, NF.TrigField a) =>
  -- | how to embed a 'Double' literal
  (Double -> a) ->
  -- | value of the variable
  a ->
  Expr ->
  a
evalExpr lit x = go
  where
    go Var = x
    go (Lit c) = lit c
    go (AddE u v) = go u NA.+ go v
    go (NegE u) = NA.negate (go u)
    go (MulE u v) = go u NM.* go v
    go (RecipE u) = NM.recip (go u)
    go (ExpE u) = NF.exp (go u)
    go (LogE u) = NF.log (go u)
    go (SinE u) = NF.sin (go u)
    go (CosE u) = NF.cos (go u)

-- | Evaluate at a 'Double' point.
evalDouble :: Double -> Expr -> Double
evalDouble x e = evalExpr id x e

-- | Evaluate into a 'Jet' series of order @k@ centered at @x0@.
evalJet :: Int -> Double -> Expr -> Jet Double
evalJet k x0 e = evalExpr (constant k) (variable k x0) e

-- ---------------------------------------------------------------------------
-- Symbolic derivative
-- ---------------------------------------------------------------------------

-- | Symbolic derivative with respect to the variable.
derivativeExpr :: Expr -> Expr
derivativeExpr Var = Lit 1
derivativeExpr (Lit _) = Lit 0
derivativeExpr (AddE u v) = AddE (derivativeExpr u) (derivativeExpr v)
derivativeExpr (NegE u) = NegE (derivativeExpr u)
derivativeExpr (MulE u v) =
  AddE (MulE (derivativeExpr u) v) (MulE u (derivativeExpr v))
derivativeExpr (RecipE u) =
  NegE (MulE (derivativeExpr u) (RecipE (MulE u u)))
derivativeExpr (ExpE u) = MulE (ExpE u) (derivativeExpr u)
derivativeExpr (LogE u) = MulE (RecipE u) (derivativeExpr u)
derivativeExpr (SinE u) = MulE (CosE u) (derivativeExpr u)
derivativeExpr (CosE u) = NegE (MulE (SinE u) (derivativeExpr u))

-- | Exact reverse-mode 'Diff' from an expression.
diffExpr :: Expr -> Diff p Double Double
diffExpr e =
  Diff $ \x ->
    let y = evalDouble x e
        dy = evalDouble x (derivativeExpr e)
     in (y, \d -> d * dy)

-- ---------------------------------------------------------------------------
-- Taylor tower
-- ---------------------------------------------------------------------------

-- | First @k@ raw derivatives of an expression at @x0@ via the 'Jet'
-- recurrence engine.  Exact (up to floating-point roundoff) — no
-- finite differences.
taylorExpr :: Expr -> Double -> Int -> [Double]
taylorExpr e x0 k =
  taylor (\x -> evalExpr (constant k) x e) k x0

-- | Exact @n@-th derivative of an expression at @x0@.
derivativeNExpr :: Expr -> Double -> Int -> Double
derivativeNExpr e x0 n
  | n < 0 = P.error "derivativeNExpr: negative order"
  | otherwise = taylorExpr e x0 n !! n
