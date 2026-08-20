{-# LANGUAGE PatternSynonyms #-}

-- | Differentiable knot-body wrapper for 'Circuit.Thread'.
--
-- 'DiffThread' is just the cartesian instance @Thread (,) (Diff' p)@ made
-- explicit, with 'Diff''-specific runners and a convenient 'knotThread'
-- constructor.
--
-- The point is to phrase differentiable stateful circuits in the same
-- vocabulary as the rest of the ecosystem: a 'Thread' is a morphism that
-- threads an ambient state wire, and a 'Loop' hides that wire with a trace.
-- 'Diff'' already interprets 'Loop' and 'Net'; this module adds the
-- intermediate "differentiable thread" type that matches 'Thread'.
module Circuit.Diff.Thread
  ( -- * Differentiable thread
    DiffThread,
    diffThread,
    runDiffThread,

    -- * Knotting
    knotThread,

    -- * Re-exports
    Thread (..),
  )
where

import Circuit.Diff (Diff', runDiff)
import Circuit.Loop (Loop (..))
import Circuit.Thread (Thread (..), threadToLoop)
import Prelude

-- | A differentiable thread: state @s@, input @a@, output @b@.
type DiffThread p s a b = Thread (,) (Diff' p) s a b

-- | Build a differentiable thread from its knot body.
diffThread :: Diff' p (s, a) (s, b) -> DiffThread p s a b
diffThread = Thread

-- | Run a differentiable thread forward.
--
-- The backward pullback is still available through 'runDiff' on the
-- underlying 'Diff'' morphism.
runDiffThread :: DiffThread p s a b -> (s, a) -> (s, b)
runDiffThread t sa = fst (runDiff (runThread t) sa)

-- | Hide the state wire of a differentiable thread, producing a 'Loop'.
knotThread :: DiffThread p s a b -> Loop (,) (Diff' p) a b
knotThread = threadToLoop

-- $setup
-- >>> import Circuit.Diff (Diff, pattern Diff)
-- >>> import Circuit.Diff.Circuit (traceNFrom)
--
-- >>> let body = Diff (\(s, a) -> ((s + a, a), \(ds', _) -> (ds', 0))) :: Diff () (Double, Double) (Double, Double)
-- >>> runDiffThread (diffThread body) (0, 1)
-- (1.0,1.0)
-- >>> fst (runDiff (traceNFrom 0 10 body) 1)
-- 1.0
