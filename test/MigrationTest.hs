module MigrationTest where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map.Strict (Map)
import Data.List (find, foldl')
import Data.Maybe (fromJust, fromMaybe)
import Test.Hspec

import TTpaola.Consent
import TTpaola.Examples.FoodDelivery (delta1, delta2, foodDelivery)
import TTpaola.Runtime
import TTpaola.Syntax
import TTpaola.TypeChecker
import TTpaola.TypedInterpreter (instAnn)
import TTpaola.Types


ct :: ClassTable
ct = either (error . show) id (inferMethodMeta (buildClassTable foodDelivery))

classDecl :: ClassName -> ClassDecl
classDecl c = ctClasses ct Map.! c

method :: ClassName -> MethodName -> MethodDecl
method c m =
  fromJust (find (\md -> mdName md == m) (cdMethods (classDecl c)))

checkMethod :: ClassName -> MethodName -> (CnstrSet, Set VarName, Duration)
checkMethod c m =
  let md = method c m
      (cn, um) = either (error . show) id (typeCheckMethod ct c md)
      dOut = either (error . show) id (methodDeltaOut ct c md)
   in (cn, um, dOut)


syntheticEnvs :: ClassName -> MethodName -> (Map FieldName TaggedVal, Map VarName TaggedVal)
syntheticEnvs c m =
  let cls = classDecl c
      md = method c m
      phi = Map.fromList [(fn, taggedField ty) | (ty, fn) <- cdFields cls]
      sigma = Map.fromList [(pn, taggedParam ty pn) | (ty, pn) <- mdParams md]
   in (phi, sigma)
 where
  taggedField :: Type -> TaggedVal
  taggedField (TClass _) = TaggedVal (VObjId_ "o") RTagEmpty
  taggedField _          = TaggedVal (VInt_ 0)   RTagEmpty

  taggedParam :: Type -> String -> TaggedVal
  taggedParam TUser nm         = TaggedVal (VUserId_ nm) RTagEmpty
  taggedParam (TClass _) _     = TaggedVal (VObjId_ "o") RTagEmpty
  taggedParam (TPersonal _) nm = TaggedVal (VInt_ 0) (RTag (Set.singleton nm) (Set.singleton "Delivery"))
  taggedParam TInt _           = TaggedVal (VInt_ 0) RTagEmpty
  taggedParam TBool _          = TaggedVal (VBool_ False) RTagEmpty
  taggedParam TUnit _          = TaggedVal VUnit_ RTagEmpty

methodUc :: ClassName -> MethodName -> Set UserId
methodUc c m =
  let (cn, _, _) = checkMethod c m
      (phi, sigma) = syntheticEnvs c m
   in Set.unions [tagUsers (instAnn ann phi sigma) | ACnstr _ ann _ _ <- Set.toList cn]

methodUm :: ClassName -> MethodName -> Set UserId
methodUm c m =
  let (_, umVars, _) = checkMethod c m
      (_, sigma) = syntheticEnvs c m
   in Set.map (\x -> let TaggedVal (VUserId_ u) _ = sigma Map.! x in u) umVars

-- Example 2 Sigma0 plus Courier consent from setAddrCons (delta1 = 11).
bootstrapWithCourier :: ConsentEnv
bootstrapWithCourier =
  foldr
    (\(u, c, a, p, e) sig -> addConsent sig u c a p e)
    Map.empty
    [ ("alice", "Plat",    Use,      "Delivery", 80)
    , ("alice", "Plat",    Collect,  "Delivery", 80)
    , ("alice", "Plat",    Transfer, "Delivery", 80)
    , ("alice", "Courier", Use,      "Delivery", delta1)
    , ("alice", "Courier", Collect,  "Delivery", delta1)
    , ("alice", "Courier", Transfer, "Delivery", delta1)
    ]


activates :: ConsentEnv -> ClassName -> Int -> Bool
activates sigma calleeClass tau =
  let (cn, _, _) = checkMethod calleeClass "deliver"
      (phi, sigmaParams) = syntheticEnvsAlice calleeClass "deliver"
   in all (constraintOk sigma calleeClass phi sigmaParams tau) (Set.toList cn)
 where
  -- Mirrors InstCnstr: act in A(Sigma[Delta]_tau, C, InstAnn(Lambda), tau+delta).
  constraintOk sig acc phi sg tau' (ACnstr act ann acDelta dur) =
    let tg = instAnn ann phi sg
        sigma' = applyAcDelta sig sg acDelta tau'
     in act `Set.member` allowedActions sigma' acc tg (tau' + dur)

  applyAcDelta sig sg acDelta tau0 =
    foldl'
      ( \s (x, r) ->
          let TaggedVal (VUserId_ u) _ = sg Map.! x
           in Map.alter (\mchi -> Just (plcyR r (fromMaybe Map.empty mchi) tau0)) u s
      )
      sig
      [ (x, r) | (x, RTUser r) <- Map.toList acDelta ]

  plcyR PBase chi _ = chi
  plcyR (PAdd r cname act p dur) chi tau0 =
    let chi' = plcyR r chi tau0
        newEntry = CE cname p (tau0 + dur)
        ins Nothing = Set.singleton newEntry
        ins (Just es) =
          let (same, _) = Set.partition (\e -> ceClass e == cname && cePurpose e == p) es
           in if Set.null same
                then Set.insert newEntry es
                else Set.insert newEntry (Set.difference es same)
     in Map.alter (Just . ins) act chi'


syntheticEnvsAlice :: ClassName -> MethodName -> (Map FieldName TaggedVal, Map VarName TaggedVal)
syntheticEnvsAlice c m =
  let cls = classDecl c
      md = method c m
      phi = Map.fromList [(fn, taggedField ty) | (ty, fn) <- cdFields cls]
      sigma = Map.fromList [(pn, taggedParam ty "alice") | (ty, pn) <- mdParams md]
   in (phi, sigma)
 where
  taggedField :: Type -> TaggedVal
  taggedField (TClass _) = TaggedVal (VObjId_ "o") RTagEmpty
  taggedField _          = TaggedVal (VInt_ 0) RTagEmpty
  taggedParam :: Type -> UserId -> TaggedVal
  taggedParam TUser u          = TaggedVal (VUserId_ u) RTagEmpty
  taggedParam (TClass _) _     = TaggedVal (VObjId_ "o") RTagEmpty
  taggedParam (TPersonal _) u  = TaggedVal (VInt_ 0) (RTag (Set.singleton u) (Set.singleton "Delivery"))
  taggedParam TInt _           = TaggedVal (VInt_ 0) RTagEmpty
  taggedParam TBool _          = TaggedVal (VBool_ False) RTagEmpty
  taggedParam TUnit _          = TaggedVal VUnit_ RTagEmpty


spec :: Spec
spec = describe "TTpaola migration (Entity to Class, get to fetch, delay delta.e to delay delta)" $ do

  describe "#2 setAddrCons" $ do
    it "Cn = empty set" $ do
      let (cn, _, _) = checkMethod "Plat" "setAddrCons"
      cn `shouldBe` Set.empty
    it "delta_out = 0" $ do
      let (_, _, d) = checkMethod "Plat" "setAddrCons"
      d `shouldBe` 0
    it "Um = {u1}" $ do
      let (_, um, _) = checkMethod "Plat" "setAddrCons"
      um `shouldBe` Set.singleton "u1"
    it "Uc = empty set" $ do
      methodUc "Plat" "setAddrCons" `shouldBe` Set.empty

  describe "#3 renewCons" $ do
    it "Cn = empty set" $ do
      let (cn, _, _) = checkMethod "Plat" "renewCons"
      cn `shouldBe` Set.empty
    it "delta_out = 0" $ do
      let (_, _, d) = checkMethod "Plat" "renewCons"
      d `shouldBe` 0
    it "Um = {u4}" $ do
      let (_, um, _) = checkMethod "Plat" "renewCons"
      um `shouldBe` Set.singleton "u4"
    it "Uc = empty set" $ do
      methodUc "Plat" "renewCons" `shouldBe` Set.empty

  describe "#4 getAddr" $ do
    it "Cn contains Use, Collect and Transfer (at dur = 1)" $ do
      let (cn, _, _) = checkMethod "Plat" "getAddr"
          actions = Set.map acAction cn
          durs = Set.map acDur cn
      actions `shouldBe` Set.fromList [Use, Collect, Transfer]
      durs `shouldBe` Set.singleton 1
    it "delta_out = 1" $ do
      let (_, _, d) = checkMethod "Plat" "getAddr"
      d `shouldBe` 1
    it "Um = empty set" $ do
      let (_, um, _) = checkMethod "Plat" "getAddr"
      um `shouldBe` Set.empty
    it "Uc = {u2}" $ do
      methodUc "Plat" "getAddr" `shouldBe` Set.singleton "u2"

  describe "#5 deliver" $ do
    it "Cn actions include Use and Collect (paper: fetch constraints)" $ do
      let (cn, _, _) = checkMethod "Courier" "deliver"
          actions = Set.map acAction cn
      Set.fromList [Use, Collect] `Set.isSubsetOf` actions `shouldBe` True
    it "Max constraint dur is 4 (fetch timeout offset)" $ do
      let (cn, _, _) = checkMethod "Courier" "deliver"
          durs = Set.map acDur cn
      maximum durs `shouldBe` 4
    it "delta_out = 14 (= 4 + max(5,10))" $ do
      let (_, _, d) = checkMethod "Courier" "deliver"
      d `shouldBe` 14
    it "Um = empty set" $ do
      let (_, um, _) = checkMethod "Courier" "deliver"
      um `shouldBe` Set.empty
    it "Uc = {u3}" $ do
      methodUc "Courier" "deliver" `shouldBe` Set.singleton "u3"

  describe "#6/#7 interference" $ do
    it "deliver and getAddr do not interfere (both Um = empty set)" $ do
      let umD = methodUm "Courier" "deliver"
          umG = methodUm "Plat" "getAddr"
          ucD = methodUc "Courier" "deliver"
          ucG = methodUc "Plat" "getAddr"
      Set.null (umD `Set.intersection` umG) `shouldBe` True
      Set.null (umD `Set.intersection` ucG) `shouldBe` True
      Set.null (umG `Set.intersection` ucD) `shouldBe` True
    it "renewCons and deliver interfere (Um intersection Uc = {alice})" $ do
      let (_, umRv, _) = checkMethod "Plat" "renewCons"
          (_, sigmaR) = syntheticEnvsAlice "Plat" "renewCons"
          umR = Set.map (\x -> let TaggedVal (VUserId_ u) _ = sigmaR Map.! x in u) umRv
          (cnD, _, _) = checkMethod "Courier" "deliver"
          (phiD, sigmaD) = syntheticEnvsAlice "Courier" "deliver"
          ucD =
            Set.unions
              [tagUsers (instAnn ann phiD sigmaD) | ACnstr _ ann _ _ <- Set.toList cnD]
      umR `Set.intersection` ucD `shouldBe` Set.singleton "alice"

  describe "#8/#9 activation timing" $ do
    it "deliver at tau=0 with expiry delta1=11 is accepted (0+4 <= 11)" $ do
      activates bootstrapWithCourier "Courier" 0 `shouldBe` True
    it "deliver at tau=8 with expiry delta1=11 is rejected (8+4=12 > 11)" $ do
      activates bootstrapWithCourier "Courier" 8 `shouldBe` False

  describe "#10 overwrite: renewCons at tau=1 (Scenario 3)" $ do
    let sigmaAfterRenew =
          foldr
            (\(c, a, p, e) sig -> addConsent sig "alice" c a p e)
            bootstrapWithCourier
            [ ("Courier", Use,      "Delivery", 1 + delta2)
            , ("Courier", Transfer, "Delivery", 1 + delta2)
            ]
        useEntry =
          maybe Set.empty id (Map.lookup "alice" sigmaAfterRenew >>= Map.lookup Use)
        colEntry =
          maybe Set.empty id (Map.lookup "alice" sigmaAfterRenew >>= Map.lookup Collect)
        traEntry =
          maybe Set.empty id (Map.lookup "alice" sigmaAfterRenew >>= Map.lookup Transfer)
    it "use expiry overwritten to 1+delta2 = 7" $ do
      Set.map ceExpiry (Set.filter (\e -> ceClass e == "Courier") useEntry)
        `shouldBe` Set.singleton (1 + delta2)
    it "transfer expiry overwritten to 1+delta2 = 7" $ do
      Set.map ceExpiry (Set.filter (\e -> ceClass e == "Courier") traEntry)
        `shouldBe` Set.singleton (1 + delta2)
    it "collect expiry stays at delta1 = 11 (not renewed)" $ do
      Set.map ceExpiry (Set.filter (\e -> ceClass e == "Courier") colEntry)
        `shouldBe` Set.singleton delta1

  describe "#11 activation after overwrite" $ do
    let sigmaAfterRenew =
          foldr
            (\(c, a, p, e) sig -> addConsent sig "alice" c a p e)
            bootstrapWithCourier
            [ ("Courier", Use,      "Delivery", 1 + delta2)
            , ("Courier", Transfer, "Delivery", 1 + delta2)
            ]
    it "deliver at tau=4 is rejected (4+4=8 > use/trans expiry 7)" $ do
      activates sigmaAfterRenew "Courier" 4 `shouldBe` False

  describe "#12 RemExpired" $ do
    it "at tau=delta1+1 all Courier entries are removed" $ do
      let sigma' = remExpired bootstrapWithCourier (delta1 + 1)
          courierEntries =
            [ e
            | (_, pm) <- Map.toList sigma'
            , (_, es) <- Map.toList pm
            , e <- Set.toList es
            , ceClass e == "Courier"
            ]
      courierEntries `shouldBe` []
    it "deliver at tau=delta1+1 is rejected" $ do
      let sigma' = remExpired bootstrapWithCourier (delta1 + 1)
      activates sigma' "Courier" (delta1 + 1) `shouldBe` False

  describe "#13/#14 fetch timeout behavior (via interpreter)" $ do
    it "fetch constraint offset is 4" $ do
      let (cn, _, _) = checkMethod "Courier" "deliver"
          fetchDurs = Set.filter (== 4) (Set.map acDur cn)
      Set.null fetchDurs `shouldBe` False
    it "delta_out exceeds fetch timeout (Ok branch reachable in time)" $ do
      let (_, _, dOut) = checkMethod "Courier" "deliver"
      dOut > 4 `shouldBe` True

  describe "consentLeq preorder" $ do
    it "longer expiry is greater in the preorder" $ do
      let s1 = addConsent Map.empty "alice" "Courier" Use "Delivery" 10
          s2 = addConsent Map.empty "alice" "Courier" Use "Delivery" 20
      consentLeq s1 s2 `shouldBe` True
      consentLeq s2 s1 `shouldBe` False
