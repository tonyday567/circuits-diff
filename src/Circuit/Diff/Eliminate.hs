{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Star-elimination of @(,)@ knots in linear 'Pullback' nets.
--
-- A 'Net (,) (,) Pullback' built by 'Circuit.Diff.Backprop.linearizeAt' is linear by
-- construction: every 'Lift' is a pointwise pullback, every 'Compose' is
-- function composition, and every 'Knot' ties an affine feedback equation.
-- This module eliminates those knots in closed form using the Kleene star
-- ('NumHask.Algebra.Ring.StarSemiring' for scalar channels,
-- 'Circuit.Mat.Dense.starMatrix' for vector channels).
--
-- The pass is /structural/: it recurses through the net, replaces each
-- 'Knot' — innermost first, Bekić order — with a single solved 'Lift', and
-- leaves every other constructor in place.  The result preserves the net's
-- shape minus its loops, so it can be evaluated on strict carriers without
-- the lazy-knot divergence that 'Traced' @Pullback (,)@ suffers when channel
-- self-coupling is non-zero — and it remains inspectable: the only opaque
-- nodes are the ones Gaussian elimination genuinely created.
--
-- The channel structure is read from 'StarEvidence' carried by the 'Knot'
-- constructor itself.  'NoEvidence' is a hard error: callers must supply
-- evidence when building the knot (or via a linearization pass that preserves
-- it).  This removes both the value-irrelevant witness and the 'unsafeCoerce'
-- that the pre-evidence design required.
module Circuit.Diff.Eliminate
  ( -- * Evidence constructors
    fieldStarEvidence,
    listEvidence,

    -- * Structural melting
    melt,

    -- * Trace elimination
    eliminateKnots,
  )
where

import Circuit.Dagger (CopyT (..), DiscardT (..), MergeT (..), ZeroT (..))
import Circuit.Dagger qualified
import Circuit.Diff.Pullback (Pullback (..))
import Circuit.Layer (run)
import Circuit.Mat.Dense (Matrix (..), fromLists, matVec, starMatrix, toLists)
import Circuit.Net (ChannelEvidence (..), Net (..))
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import NumHask.Free.Carriers (FieldStar (..))
import Prelude hiding (id, (.))
import Prelude qualified as P

-- $setup
-- >>> import Circuit.Diff.Pullback (Pullback (..), evalPullback)
-- >>> import Circuit.Net (Net (..))
-- >>> import NumHask.Free.Carriers (FieldStar (..))
-- >>> import Prelude hiding (id, (.))

-- | Replace every structural row with its pure 'Pullback' interpretation.
--
-- 'Circuit.Net.melt' melts bimonoid rows ('Copy', 'Discard', 'Plus',
-- 'Zero') by /running/ the net.  That is fine for knot-free wiring, but it
-- eagerly ties any lazy 'Knot' encountered along the way — so a net with
-- non-zero channel self-coupling diverges before a subsequent star-elimination
-- pass can save it.
--
-- This pass performs the same row elimination /without/ running anything.
-- Each structural row is replaced by the corresponding 'Pullback' arrow,
-- lifted into a 'Net' node.  The result is semantically equivalent but
-- contains only 'Lift', 'Compose', 'Swap', 'Par' and 'Knot' constructors.
-- After melting, 'eliminateKnots' can remove the knots in closed form.
melt :: Net (,) (,) Pullback a b -> Net (,) (,) Pullback a b
melt = \case
  Lift p -> Lift p
  Compose g f -> Compose (melt g) (melt f)
  Par f g -> Par (melt f) (melt g)
  Swap -> Swap
  Knot ev f -> Knot ev (melt f)
  Copy -> Lift copyT
  Discard -> Lift (discardT @(,))
  Plus -> Lift plusT
  Zero -> Lift (zeroT @(,))

-- | Evidence for a one-dimensional 'FieldStar' channel.
--
-- The matrix carrier is @'Matrix' 'FieldStar'@ — a 1×1 matrix whose single
-- element is the scalar channel cotangent.
fieldStarEvidence :: ChannelEvidence FieldStar
fieldStarEvidence =
  StarEvidence
    { channelDimE = 1,
      zeroChannelE = const NHA.zero,
      basisChannelE = \_ _ -> NHM.one,
      addChannelE = (NHA.+),
      negateChannelE = NHA.negate,
      selfMatrixE = \_ f -> fromLists [[f NHM.one]],
      applyMatrixE = \m v -> case toLists m of
        [[s]] -> s NHM.* v
        _ -> error "Circuit.Diff.Eliminate.applyMatrixE: scalar channel expected a 1x1 matrix",
      starMatrixE = starMatrix
    }

-- | Evidence for an n-dimensional list channel.
--
-- The matrix carrier is @'Matrix' a@; the channel cotangent is @[a]@.
listEvidence ::
  ( NHR.StarSemiring a,
    NHA.Subtractive a
  ) =>
  Int ->
  ChannelEvidence [a]
listEvidence dim =
  let basis n i = [if k == i then NHM.one else NHA.zero | k <- [0 .. n - 1]]
      zero n = replicate n NHA.zero
   in StarEvidence
        { channelDimE = dim,
          zeroChannelE = zero,
          basisChannelE = basis,
          addChannelE = zipWith (NHA.+),
          negateChannelE = fmap NHA.negate,
          selfMatrixE = \n f ->
            let cols = [f (basis n i) | i <- [0 .. n - 1]]
             in fromLists [[col P.!! k | col <- cols] | k <- [0 .. n - 1]],
          applyMatrixE = matVec,
          starMatrixE = starMatrix
        }

-- | 'FieldStar' as a numeric carrier for circuits' additive structure, so
-- hand-built nets can use structural rows at 'FieldStar' types.  (Nets from
-- 'Circuit.Diff.Backprop.linearizeAt' never need this — their structural rows are
-- already 'Lift's.)
--
-- These instances remain necessary because structural rows ('Plus', 'Zero')
-- carry 'MergeT' / 'ZeroT' constraints that resolve to 'Merge' / 'Zero' on
-- the wiring arrow.  For 'Pullback FieldStar' those constraints bottom out in
-- 'Merge (->) FieldStar' and 'Zero (->) FieldStar'.  The evidence design does
-- not change this: it supplies star-elimination structure, not the bimonoid
-- merge/zero dictionaries.  Deliberately orphan: this module is the federation
-- seam between @circuits@ and @numhask-free@.
instance Circuit.Dagger.Merge (->) FieldStar where
  plus (FieldStar x, FieldStar y) = FieldStar (x P.+ y)

instance Circuit.Dagger.Zero (->) FieldStar where
  zero _ = FieldStar 0

-- | Solve one affine knot body in closed form.
--
-- For a body @f :: (j, c) -> (j, b)@ (channel cotangent, output cotangent),
-- affinity gives @f₁ (dj, dc) = A·dj + C·dc@.  The probes:
--
-- > C·dc = f₁ (0, dc)                       -- one call, at the true zero
-- > A·e_i = f₁ (e_i, dc) − C·dc             -- offset-subtracted: valid at dc ≠ 0
-- > dj   = star A · C·dc                    -- starMatrix
-- > db   = f₂ (dj, dc)                      -- one final call
--
-- The offset subtraction is what lets every probe run at the /actual/
-- cotangent @dc@, so no @zero@ for the (existential) type @c@ is ever
-- needed.  Cost: @dim + 2@ body calls per cotangent; the star is /not/
-- shared across cotangents — that is the price of the existential.
solveAffine ::
  ChannelEvidence j ->
  ((j, c) -> (j, b)) ->
  c ->
  b
solveAffine ev body dc =
  case ev of
    NoEvidence ->
      error "Circuit.Diff.Eliminate.solveAffine: Knot carries NoEvidence"
    StarEvidence
      { channelDimE = dim,
        zeroChannelE = zc,
        addChannelE = addC,
        negateChannelE = negC,
        selfMatrixE = selfM,
        applyMatrixE = applyM,
        starMatrixE = starM
      } ->
        let zeroJ = zc dim
            cdc = fst (body (zeroJ, dc))
            negCdc = negC cdc
            aMat = selfM dim (\dk -> addC (fst (body (dk, dc))) negCdc)
            dj = applyM (starM aMat) cdc
         in snd (body (dj, dc))

-- | Eliminate all @(,)@ knots in a linear pullback net, structurally.
--
-- Structural rows are melted first ('melt'); then the recursion replaces each
-- 'Knot' — innermost first, so a knot body handed to 'solveAffine' is already
-- loop-free and can be evaluated by plain 'run' — with one solved 'Lift'.
-- Everything else keeps its shape.
--
-- Every knot must carry 'StarEvidence' for its channel type.  'NoEvidence'
-- raises a clear error: the evidence is load-bearing, not an optional hint.
--
-- A self-coupled scalar loop the lazy trace diverges on, solved exactly
-- (@dj = 0.3·dj + 2·dc@, @db = dj@, so @db\/dc = 2\/0.7@):
--
-- >>> :{
-- let body (FieldStar dj, dc) = (FieldStar (0.3 * dj + 2.0 * dc), dj)
--     net = Knot fieldStarEvidence (Lift (Pullback body)) :: Net (,) (,) Pullback Double Double
-- :}
--
-- >>> let solved = eliminateKnots net
-- >>> abs (evalPullback solved 1.0 - 2.0 / 0.7) < 1e-12
-- True
eliminateKnots ::
  Net (,) (,) Pullback b a ->
  Net (,) (,) Pullback b a
eliminateKnots net = go (melt net)
  where
    go :: forall x y. Net (,) (,) Pullback x y -> Net (,) (,) Pullback x y
    go n = case n of
      Lift p -> Lift p
      Compose g f -> Compose (go g) (go f)
      Par f g -> Par (go f) (go g)
      Swap -> Swap
      Knot ev f ->
        let f' = go f -- innermost first: body is knot-free below here
            body = runPullback (run f')
         in Lift (Pullback (solveAffine ev body))
      Copy -> unreachableRow "Copy"
      Discard -> unreachableRow "Discard"
      Plus -> unreachableRow "Plus"
      Zero -> unreachableRow "Zero"

    unreachableRow name =
      error $
        "Circuit.Diff.Eliminate.eliminateKnots: structural "
          ++ name
          ++ " row after melt (impossible)"
