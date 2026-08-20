{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}

-- | Carrier injection for polymorphic differentiable models.
--
-- When a physical right-hand side is written once and polymorphic in a
-- numeric carrier, constants must be lifted into that carrier.  'Lit'
-- provides the overload: instantiating at 'Double' gives forward simulation;
-- instantiating at @'Diff'' p 'Double' 'Double'@ gives reverse-mode
-- derivatives of every intermediate.
module Circuit.Diff.Carrier
  ( Lit (..),
  )
where

import Circuit.Diff.Circuit (Diff', pattern Diff)
import Prelude

-- | Lift a numeric literal into the active carrier.
--
-- @
-- instance Lit Double where lit = id
-- instance Lit (Diff' p Double Double) where lit c = Diff (const (c, const 0))
-- @
--
-- Every coefficient in a polymorphic model can be written @'lit' c@ once,
-- and resolves correctly under both simulation and differentiation.
class Lit a where
  lit :: Double -> a

instance Lit Double where
  lit = id

instance Lit (Diff' p Double Double) where
  lit c = Diff (const (c, const 0))
