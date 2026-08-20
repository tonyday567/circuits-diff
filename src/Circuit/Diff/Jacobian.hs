{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Column-style Jacobian construction via reverse-mode AD.
--
-- Build ∂f/∂x for a list-valued function by seeding one input component at a
-- time through 'Circuit.Diff.Circuit.Diff'' and reading back the pullbacks.
-- This is the reusable pattern underlying the Daisyworld / DubinsChase oracle
-- style: write the physics once, polymorphic in a carrier with 'Lit', then
-- instantiate the Jacobian helper at 'Double'.
module Circuit.Diff.Jacobian
  ( jacobianFrom,
  )
where

import Circuit.Diff.Carrier (Lit (..))
import Circuit.Diff.Circuit (Diff', pattern Diff, runDiff)
import Prelude

-- | Jacobian of @f : R^n -> R^m@ at a point, built column-by-column.
--
-- The supplied function must already be instantiated at the 'Diff'' carrier;
-- callers typically wrap a polymorphic model:
--
-- @
-- jacobianFrom s0 (\s -> daisyRHS (lit l) s)
-- @
--
-- Returns an @m × n@ list of lists: outer index is output component, inner
-- index is input component.
jacobianFrom ::
  forall tag.
  [Double] ->
  ([Diff' tag Double Double] -> [Diff' tag Double Double]) ->
  [[Double]]
jacobianFrom s0 f =
  let n = length s0
      m = length (f (map lit s0))
      col k =
        let seed = Diff (,id) :: Diff' tag Double Double
            s = [if i == k then seed else lit (s0 !! i) | i <- [0 .. n - 1]]
            outs = f s
         in [let (_, pb) = runDiff (outs !! i) (s0 !! k) in pb 1 | i <- [0 .. m - 1]]
      cols = map col [0 .. n - 1]
   in [[(cols !! j) !! i | j <- [0 .. n - 1]] | i <- [0 .. m - 1]]
