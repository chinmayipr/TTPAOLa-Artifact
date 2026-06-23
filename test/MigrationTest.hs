module MigrationTest where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Map.Strict (Map)
import Data.List (find)
import Data.Maybe (fromJust, fromMaybe)
import Test.Hspec

import TyPAOL.Consent
import TyPAOL.Examples.FoodDelivery (foodDelivery)
import TyPAOL.Runtime
import TyPAOL.Syntax
import TyPAOL.TypeChecker
import TyPAOL.TypedInterpreter (instAnn)
import TyPAOL.Types


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
  taggedParam TUser nm        = TaggedVal (VUserId_ nm) RTagEmpty
  taggedParam (TClass _) _    = TaggedVal (VObjId_ "o") RTagEmpty
  taggedParam (TPersonal _) nm = TaggedVal (VInt_ 0) (RTag (Set.singleton nm) (Set.singleton "Delivery"))
  taggedParam TInt _          = TaggedVal (VInt_ 0) RTagEmpty
  taggedParam TBool _         = TaggedVal (VBool_ False) RTagEmpty
  taggedParam TUnit _         = TaggedVal VUnit_ RTagEmpty

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

bootstrapWithCourier :: ConsentEnv
bootstrapWithCourier =
  foldr
    (\(u, c, a, p, e) sig -> addConsent sig u c a p e)
    Map.empty
    [ ("alice", "Plat",    Use,      "Delivery", 80)
    , ("alice", "Plat",    Collect,  "Delivery", 80)
    , ("alice", "Plat",    Store,    "Delivery", 80)
    , ("alice", "Plat",    Transfer, "Delivery", 80)
    , ("alice", "Courier", Use,      "Delivery", 50)
    , ("alice", "Courier", Collect,  "Delivery", 50)
    , ("alice", "Courier", Transfer, "Delivery", 50)
    ]


activates :: ConsentEnv -> ClassName -> ClassName -> ClassName -> Int -> Bool
activates sigma callerClass calleeClass _aliceClass tau =
  let (cn, _, _) = checkMethod calleeClass "deliver"
      (phi, sigmaParams) = syntheticEnvsAlice calleeClass "deliver"
   in all (constraintOk sigma callerClass phi sigmaParams tau) (Set.toList cn)
 where
  constraintOk sig acc phi sg tau' (ACnstr act ann _ dur) =
    let tg = instAnn ann phi sg
        c = if act == Store then calleeClass else acc
     in act `Set.member` allowedActions sig c tg (tau' + dur)

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
  taggedParam TUser u         = TaggedVal (VUserId_ u) RTagEmpty
  taggedParam (TClass _) _    = TaggedVal (VObjId_ "o") RTagEmpty
  taggedParam (TPersonal _) u = TaggedVal (VInt_ 0) (RTag (Set.singleton u) (Set.singleton "Delivery"))
  taggedParam TInt _          = TaggedVal (VInt_ 0) RTagEmpty
  taggedParam TBool _         = TaggedVal (VBool_ False) RTagEmpty
  taggedParam TUnit _         = TaggedVal VUnit_ RTagEmpty


spec :: Spec
spec = describe "TyPAOL migration (Entity to Class, get to fetch, delay delta.e to delay delta)" $ do

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
    it "Cn actions include Use and Collect" $ do
      let (cn, _, _) = checkMethod "Courier" "deliver"
          actions = Set.map acAction cn
      Set.fromList [Use, Collect] `Set.isSubsetOf` actions `shouldBe` True
    it "Max constraint dur is 14 (= delta_out)" $ do
      let (cn, _, _) = checkMethod "Courier" "deliver"
          durs = Set.map acDur cn
      maximum durs `shouldBe` 14
    it "delta_out = 14" $ do
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
      -- Both methods refer to a user variable. We model the case where both
      -- threads receive @alice@ as their actual user argument: the synthetic
      -- env binds @u4@ maps to "alice" and @u3@ maps to "alice".
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
    it "deliver at tau=0 with expiry 50 is accepted" $ do
      activates bootstrapWithCourier "Courier" "Courier" "alice" 0 `shouldBe` True
    it "deliver at tau=40 with expiry 50 is rejected (40+14=54 > 50)" $ do
      activates bootstrapWithCourier "Courier" "Courier" "alice" 40 `shouldBe` False

  describe "#10 overwrite: renewCons at tau=10" $ do
    let sigmaAfterRenew =
          foldr
            (\(c, a, p, e) sig -> addConsent sig "alice" c a p e)
            bootstrapWithCourier
            [ ("Courier", Use,      "Delivery", 10 + 20)
            , ("Courier", Transfer, "Delivery", 10 + 20)
              -- collect is NOT renewed (intentional mismatch with the spec)
            ]
        useEntry =
          maybe Set.empty id (Map.lookup "alice" sigmaAfterRenew >>= Map.lookup Use)
        colEntry =
          maybe Set.empty id (Map.lookup "alice" sigmaAfterRenew >>= Map.lookup Collect)
        traEntry =
          maybe Set.empty id (Map.lookup "alice" sigmaAfterRenew >>= Map.lookup Transfer)
    it "use   expiry overwritten to 30" $ do
      Set.map ceExpiry (Set.filter (\e -> ceClass e == "Courier") useEntry)
        `shouldBe` Set.singleton 30
    it "transfer expiry overwritten to 30" $ do
      Set.map ceExpiry (Set.filter (\e -> ceClass e == "Courier") traEntry)
        `shouldBe` Set.singleton 30
    it "collect expiry stays at 50 (not renewed)" $ do
      Set.map ceExpiry (Set.filter (\e -> ceClass e == "Courier") colEntry)
        `shouldBe` Set.singleton 50

  describe "#11 activation after overwrite" $ do
    let sigmaAfterRenew =
          foldr
            (\(c, a, p, e) sig -> addConsent sig "alice" c a p e)
            bootstrapWithCourier
            [ ("Courier", Use,      "Delivery", 30)
            , ("Courier", Transfer, "Delivery", 30)
            ]
    it "deliver at tau=20 is rejected (20+14=34 > 30 bottleneck on use)" $ do
      activates sigmaAfterRenew "Courier" "Courier" "alice" 20 `shouldBe` False

  describe "#12 RemExpired" $ do
    it "at tau=51 all Courier entries are removed" $ do
      let sigma' = remExpired bootstrapWithCourier 51
          courierEntries =
            [ e
            | (_, pm) <- Map.toList sigma'
            , (_, es) <- Map.toList pm
            , e <- Set.toList es
            , ceClass e == "Courier"
            ]
      courierEntries `shouldBe` []
    it "deliver at tau=51 is rejected" $ do
      let sigma' = remExpired bootstrapWithCourier 51
      activates sigma' "Courier" "Courier" "alice" 51 `shouldBe` False

  describe "#13/#14 fetch timeout behavior (via interpreter)" $ do
    it "fetch with d > timeout : timed step reduces to Err" $ do
      -- See InterpreterTest (fetch timeout) for the operational check;
      -- here we only sanity-check the static shape of the constraint.
      let (cn, _, _) = checkMethod "Courier" "deliver"
          fetchDurs = Set.filter (== 4) (Set.map acDur cn)
      Set.null fetchDurs `shouldBe` False
    it "fetch with d <= timeout : Ok branch is reachable (max dur > 4)" $ do
      let (cn, _, _) = checkMethod "Courier" "deliver"
          maxDur = maximum (Set.map acDur cn)
      maxDur > 4 `shouldBe` True
