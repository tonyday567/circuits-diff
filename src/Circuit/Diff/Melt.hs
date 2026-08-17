-- | Pure structural melting for 'Net Pullback'.
--
-- 'Circuit.Net.melt' melts bimonoid rows ('Copy', 'Discard', 'Plus',
-- 'Zero') by /running/ the net.  That is fine for knot-free wiring, but it
-- eagerly ties any lazy 'Trace' encountered along the way — so a net with
-- non-zero channel self-coupling diverges before a subsequent star-elimination
-- pass can save it.
--
-- This pass performs the same row elimination /without/ running anything.
-- Each structural row is replaced by the corresponding 'Pullback' arrow,
-- lifted into a 'Net' node.  The result is semantically equivalent but
-- contains only 'Lift', 'Compose', 'Swap', 'Par' and 'Knot' constructors.
-- After melting, 'Circuit.Diff.Eliminate.eliminateKnots' can remove the knots
-- in closed form.
module Circuit.Diff.Melt
  ( melt,
  )
where

import Circuit.Dagger (Copy (..), Discard (..), Merge (..), Zero (..))
import Circuit.Diff.Pullback (Pullback (..))
import Circuit.Net (Net (..))
import Prelude hiding (id, (.))

-- | Replace every structural row with its pure 'Pullback' interpretation.
--
-- The 'Bimonoid' constraints carried by 'Copy', 'Discard', 'Plus' and 'Zero'
-- guarantee that the corresponding 'Comonoid' / 'Monoid' methods exist for
-- 'Pullback', so melting needs no forward execution.
melt :: Net (,) Pullback a b -> Net (,) Pullback a b
melt = \case
  Lift p -> Lift p
  Compose g f -> Compose (melt g) (melt f)
  Par f g -> Par (melt f) (melt g)
  Swap -> Swap
  Knot f -> Knot (melt f)
  Copy -> Lift copy
  Discard -> Lift discard
  Plus -> Lift plus
  Zero -> Lift zero
