module TyPAOL.Consent where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map.Strict (Map)
import TyPAOL.Syntax (Action (..), ClassName, Purpose, UserId, Tag (..))

-- Runtime tag: concrete users, not variables.
data RTag = RTagEmpty | RTag (Set UserId) (Set Purpose)
  deriving (Eq, Ord, Show)

-- ConsentEnv maps a user to a PolicyMap; a PolicyMap maps an action to a set
-- of (class, purpose, expiry) entries. We keep the purpose field here even
-- though the paper simplifies it away.
data ConsentEntry = CE
  { ceClass :: ClassName
  , cePurpose :: Purpose
  , ceExpiry :: Int -- absolute time
  }
  deriving (Eq, Ord, Show)

type PolicyMap = Map Action (Set ConsentEntry)
type ConsentEnv = Map UserId PolicyMap

tagCombine :: RTag -> RTag -> RTag
tagCombine RTagEmpty t = t
tagCombine t RTagEmpty = t
tagCombine (RTag u1 p1) (RTag u2 p2) =
  let p = Set.intersection p1 p2
   in if Set.null p then RTagEmpty else RTag (Set.union u1 u2) p

tagUsers :: RTag -> Set UserId
tagUsers RTagEmpty = Set.empty
tagUsers (RTag us _) = us

tagPurposes :: RTag -> Set Purpose
tagPurposes RTagEmpty = Set.empty
tagPurposes (RTag _ ps) = ps

tagLeq :: RTag -> RTag -> Bool
tagLeq t1 t2 = tagCombine t1 t2 == t1

-- Convert a source-level Tag to a runtime RTag. By this point the names in
-- the user-variable set are concrete user ids.
tagFromSource :: Tag -> RTag
tagFromSource TagEmpty = RTagEmpty
tagFromSource (TagExpr vars purposes) =
  RTag vars purposes

-- Source-level tag combine (for the type checker): same algebra as RTag.
tagCombineSrc :: Tag -> Tag -> Tag
tagCombineSrc TagEmpty t = t
tagCombineSrc t TagEmpty = t
tagCombineSrc (TagExpr u1 p1) (TagExpr u2 p2) =
  let p = Set.intersection p1 p2
   in if Set.null p then TagEmpty else TagExpr (Set.union u1 u2) p

tagLeqSrc :: Tag -> Tag -> Bool
tagLeqSrc t1 t2 = tagCombineSrc t1 t2 == t1

allActions :: Set Action
allActions = Set.fromList [minBound .. maxBound]

-- Check a single action directly, short-circuiting per user, without
-- materialising the full allowed-action set.
actionAllowed :: ConsentEnv -> ClassName -> Action -> RTag -> Int -> Bool
actionAllowed _ _ _ RTagEmpty _ = True
actionAllowed sigma cname act (RTag users purposes) tau
  | Set.null users = True
  | otherwise = all userOk (Set.toList users)
 where
  userOk :: UserId -> Bool
  userOk u =
    case Map.lookup u sigma >>= Map.lookup act of
      Nothing -> False
      Just entries ->
        any
          ( \e ->
              ceClass e == cname
                && cePurpose e `Set.member` purposes
                && tau <= ceExpiry e
          )
          (Set.toList entries)

-- All allowed actions for a consent environment, class, tag, and time, with
-- the class as the accountable entity.
allowedActions :: ConsentEnv -> ClassName -> RTag -> Int -> Set Action
allowedActions sigma cname t tau =
  Set.filter (\a -> actionAllowed sigma cname a t tau) allActions

complyU :: ConsentEnv -> ClassName -> RTag -> Int -> Bool
complyU sigma cname = actionAllowed sigma cname Use

complyC :: ConsentEnv -> ClassName -> RTag -> Int -> Bool
complyC sigma cname = actionAllowed sigma cname Collect

complyT :: ConsentEnv -> ClassName -> RTag -> Int -> Bool
complyT sigma cname = actionAllowed sigma cname Transfer

-- Store compliance: both the callee's class (the object) and the caller's
-- class must allow the Store action.
complyS :: ConsentEnv -> ClassName -> ClassName -> RTag -> Int -> Bool
complyS sigma cObj cCaller t tau =
  actionAllowed sigma cObj Store t tau
    && actionAllowed sigma cCaller Store t tau

addConsent :: ConsentEnv -> UserId -> ClassName -> Action -> Purpose -> Int -> ConsentEnv
addConsent sigma0 u cname act purpose absExpiry =
  Map.alter (Just . updUser) u sigma0
 where
  newEntry = CE cname purpose absExpiry
  updUser :: Maybe PolicyMap -> PolicyMap
  updUser Nothing = Map.singleton act (Set.singleton newEntry)
  updUser (Just pm) =
    Map.alter (Just . insEntry) act pm
  insEntry :: Maybe (Set ConsentEntry) -> Set ConsentEntry
  insEntry Nothing = Set.singleton newEntry
  insEntry (Just es) =
    let (same, _rest) = Set.partition (\e -> ceClass e == cname && cePurpose e == purpose) es
     in if Set.null same
          then Set.insert newEntry es
          else Set.insert newEntry (Set.difference es same)

-- Remove entries whose expiry is strictly before the given time.
remExpired :: ConsentEnv -> Int -> ConsentEnv
remExpired sigma tau =
  Map.mapMaybe pruneUser sigma
 where
  pruneUser :: PolicyMap -> Maybe PolicyMap
  pruneUser pm =
    let pm' = Map.mapMaybe pruneEntries pm
     in if Map.null pm' then Nothing else Just pm'
  pruneEntries :: Set ConsentEntry -> Maybe (Set ConsentEntry)
  pruneEntries es =
    let es' = Set.filter (\e -> ceExpiry e >= tau) es
     in if Set.null es' then Nothing else Just es'

consentLeq :: ConsentEnv -> ConsentEnv -> Bool
consentLeq s1 s2 =
  Map.keysSet s1 `Set.isSubsetOf` Map.keysSet s2
    && all (\u -> userLeq u (Map.lookup u s1) (Map.lookup u s2)) (Map.keys s1)
 where
  userLeq :: UserId -> Maybe PolicyMap -> Maybe PolicyMap -> Bool
  userLeq _ Nothing _ = True
  userLeq _ (Just _) Nothing = False
  userLeq _ (Just pm1) (Just pm2) =
    Map.keysSet pm1 `Set.isSubsetOf` Map.keysSet pm2
      && all
        ( \a ->
            maybe False (`entriesLeq` maybe Set.empty id (Map.lookup a pm2)) (Map.lookup a pm1)
        )
        (Map.keys pm1)
  entriesLeq :: Set ConsentEntry -> Set ConsentEntry -> Bool
  entriesLeq e1 e2 = e1 `Set.isSubsetOf` e2
