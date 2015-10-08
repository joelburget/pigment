-- | Well-typed edits a-la http://unisonweb.org/2015-06-12/editing.html
module ProofState.Structure.Edit where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List
import Data.Maybe

-- | Invariant: if a hash is open, its dependents in the `Edit` must also be open
data Edit h =
  Edit { closed :: Map h (Set h)
       , opened :: Map (h,h) (Map h (Set h)) }

instance Ord h => Monoid (Edit h) where
  mempty = Edit Map.empty Map.empty
  mappend (Edit c1 o1) (Edit c2 o2) = Edit c o
    where
    c = Map.unionWith Set.union c1 c2
    o = Map.unionWith (Map.unionWith Set.union) o1' o2'
    -- subtract from `o2` any entries closed by `c1`
    -- and subtract from `o1` any entries closed by `c2`
    keep c (h,h2) = maybe True (Set.notMember h2) (Map.lookup h c)
    strip c (root, deps) =
      let deps' = Map.filterWithKey (\h _ -> Map.notMember h c) deps
      in if Map.null deps' && not (keep c root) then []
         else [(root, deps')]
    o1' = Map.fromList $ Map.toList o1 >>= strip c2
    o2' = Map.fromList $ Map.toList o2 >>= strip c1

scope :: Edit h -> Set h
scope = Map.keysSet . closed

resolve :: Ord h => (Set h -> h) -> h -> Edit h -> Edit h
resolve r h (Edit closed opened) =
  Edit (Map.adjust (Set.singleton . r) h closed) opened

class Ord h => Dependencies h where
  dependencies :: h -> Set h
  dependents :: h -> Set h

transitiveDependencies :: Dependencies h => (h -> Bool) -> h -> Set h
transitiveDependencies guard h | guard h =
  let dh = dependencies h
  in dh `Set.union` (Set.unions $ map (transitiveDependencies guard) (Set.toList dh))
transitiveDependencies _ _ = Set.empty

transitiveDependents :: Dependencies h => (h -> Bool) -> h -> Set h
transitiveDependents guard h | guard h =
  let dh = dependents h
  in dh `Set.union` (Set.unions $ map (transitiveDependents guard) (Set.toList dh))
transitiveDependents _ _ = Set.empty

transitiveDependents' :: Dependencies h => h -> Set h
transitiveDependents' = transitiveDependents (const True)

-- Like `resolve`, but propagates the resolution out to transitive dependents
resolve' :: Dependencies h => (Set h -> h) -> h -> Edit h -> Edit h
resolve' r h (Edit closed opened) =
  let
    closed' = Map.adjust (Set.singleton . r) h closed
    kept = maybe Set.empty keep' (Map.lookup h closed)
    keep' hs = Set.unions . map transitiveDependents' $ Set.toList hs
    dirty = transitiveDependents (\h -> Map.member h closed') h
    prune h s =
      if Set.member h dirty then Set.filter (\h -> Set.member h kept) s
      else s
  -- for all dependents of initial change, strip out any hashes
  -- that don't depend on `kept`, the resolved hash
  in Edit (Map.mapWithKey prune closed') opened

-- | Open a hash for editing. Preserves the `Edit` invariants.
-- Thus opening a hash results in all transitive dependents referenced
-- by the `Edit` being opened as well.
open :: Dependencies h => (h -> (h, Map h h)) -> h -> Edit h -> Edit h
open breakDeps h e@(Edit closed opened) =
  -- am like 73% sure this is correct
  let
    (h', deps0) = breakDeps h
    deps = Map.map Set.singleton deps0
    hs' = Set.insert h' $ fromMaybe Set.empty (Map.lookup h closed)
    closed' = Map.delete h closed -- a hash cannot be closed and open
    addDeps s = Just $ Map.unionWith Set.union (fromMaybe Map.empty s) deps
    -- when opening, preserve existing info
    opened' = foldl (\m h' -> Map.alter addDeps (h,h') m) opened (Set.toList hs')
    -- there may be some dependents of 'h' that need to be opened to preserve invariant
    e' = Edit closed' opened'
    dirty = Map.keys (submap (dependents h) closed')
  in foldl' (\e h -> open breakDeps h e) e' dirty

-- | The submap of the input containing only keys that exist in the given
-- `Set`. Trims the map first with some `log(n)` splits, then filters remaining
-- keys in linear time. This really belongs in Data.Map.
submap :: Ord k => Set k -> Map k v -> Map k v
submap ks _ | Set.null ks = Map.empty
submap ks m =
  let
    (low,high) = (Set.findMin ks, Set.findMax ks)
    lowEdge = maybe Map.empty (Map.singleton low) (Map.lookup low m)
    highEdge = maybe Map.empty (Map.singleton high) (Map.lookup high m)
    (middle, _) = Map.split low m
    (trimmedMiddle, _) = Map.split high middle
    filteredMiddle = Map.filterWithKey (\k _ -> Set.member k ks) trimmedMiddle
  in
    lowEdge `Map.union` filteredMiddle `Map.union` highEdge
