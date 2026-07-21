{-# LANGUAGE LambdaCase #-}
-- Negative litmus tests: rules that must reject or take the
-- failure path (type error, bind refuse, fetch-adv, NI, InstCnstr/plcy).
module LitmusTest where

import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.List (find)
import Data.Maybe (fromJust)
import Test.Hspec

import TTpaola.Consent
import TTpaola.Interpreter
import TTpaola.Runtime
import TTpaola.Syntax
import TTpaola.TypeChecker
import TTpaola.TypedInterpreter (activateTyped, instCnstr)
import TTpaola.Types

runI :: InterpM a -> Config -> Either RuntimeError (a, Config)
runI m cfg = runExcept (runStateT m cfg)

tagAlice :: RTag
tagAlice = RTag (Set.singleton "alice") (Set.singleton "Delivery")

aliceTV :: TaggedVal
aliceTV = TaggedVal (VUserId_ "alice") RTagEmpty

xTagged :: TaggedVal
xTagged = TaggedVal (VInt_ 42) tagAlice

-- Class with twin(U,U) and caller that aliases the same user twice
aliasProg :: Program
aliasProg =
  Program
    { prgPurposes = ["Delivery"]
    , prgClasses =
        [ ClassDecl
            { cdName = "C"
            , cdParams = []
            , cdFields = [(TClass "C", "me")]
            , cdMethods =
                [ MethodDecl TUnit TAEmpty "twin" [(TUser, "a"), (TUser, "b")] (EVal VLitUnit)
                , MethodDecl TUnit TAEmpty "bad" [(TUser, "u")] $
                    ELet "_" TUnit
                      (EAsyncCall (VField "me") "twin" [VVar "u", VVar "u"])
                      (EVal VLitUnit)
                ]
            }
        ]
    , prgMain = []
    }

-- Method whose fetch-else is personal (must be rejected by typing).
fetchElseProg :: Program
fetchElseProg =
  Program
    { prgPurposes = ["Delivery"]
    , prgClasses =
        [ ClassDecl
            { cdName = "C"
            , cdParams = []
            , cdFields = [(TClass "C", "self")] -- unused, need a future in scope via let
            , cdMethods =
                [ MethodDecl TUnit TAEmpty "m" [(TUser, "u"), (TPersonal TInt, "x")] $
                    -- fabricate a future by async to self, then fetch with tagged else
                    ELet "f" TUnit (EAsyncCall (VField "self") "m" [VVar "u", VVar "x"]) $
                      ELet "_" (TPersonal TInt)
                        (EFetch (VVar "f") 1 (VTag (VLitInt 0) (TagExpr (Set.singleton "u") (Set.singleton "Delivery"))))
                        (EVal VLitUnit)
                ]
            }
        ]
    , prgMain = []
    }

-- grantThenUse: addCon then collect personal data (Cn depends on plcy(Delta)).
grantProg :: Program
grantProg =
  Program
    { prgPurposes = ["Delivery"]
    , prgClasses =
        [ ClassDecl
            { cdName = "Demo"
            , cdParams = []
            , cdFields = []
            , cdMethods =
                [ MethodDecl TUnit TAEmpty "grantThenUse" [(TUser, "u"), (TPersonal TInt, "x")] $
                    seqE (EAddCon (VVar "u") (Policy "Demo" Use "Delivery" 20)) $
                      seqE (EAddCon (VVar "u") (Policy "Demo" Collect "Delivery" 20)) $
                        ELet "_z" (TPersonal TInt) (EVal (VVar "x")) (EVal VLitUnit)
                ]
            }
        ]
    , prgMain = []
    }

methodOf :: Program -> ClassName -> MethodName -> MethodDecl
methodOf prog cname mname =
  fromJust $ do
    cls <- find (\c -> cdName c == cname) (prgClasses prog)
    find (\m -> mdName m == mname) (cdMethods cls)



spec :: Spec
spec = describe "TTpaola negative litmus" $ do

  describe "type reject" $ do
    it "aliased user actuals in async call" $ do
      let ct0 = buildClassTable aliasProg
      case typeCheckMethod ct0 "C" (methodOf aliasProg "C" "bad") of
        Left (TypeError msg) -> msg `shouldContain` "aliased"
        Right _ -> expectationFailure "expected type error for aliased user actuals"

    it "personal fetch-else is rejected" $ do
      let ct0 = buildClassTable fetchElseProg
      case typeCheckMethod ct0 "C" (methodOf fetchElseProg "C" "m") of
        Left (TypeError msg) -> msg `shouldContain` "else"
        Right _ -> expectationFailure "expected type error for personal fetch else"

  describe "untyped bind / fetch-adv" $ do
    it "bind refuses tagged arg without Transfer (complyT)" $ do
      let ct = either (error . show) id (inferMethodMeta (buildClassTable grantProg))
          -- Sigma has Use+Collect but not Transfer, ComplyT fails at bind.
          sig =
            foldr
              (\(a, e) s -> addConsent s "alice" "Demo" a "Delivery" e)
              Map.empty
              [(Use, 100), (Collect, 100)]
          cfg =
            Config
              { cfgObjects =
                  Map.singleton "d0" $
                    Object Map.empty Idle [] "Demo"
              , cfgMessages =
                  [ Message "grantThenUse" "d0" [aliceTV, xTagged] "f0" "Demo"
                  ]
              , cfgFutures = Map.singleton "f0" Nothing
              , cfgConsent = sig
              , cfgTime = 0
              , cfgFreshCtr = 0
              , cfgVarStore = Map.empty
              , cfgDefaultClass = "Demo"
              }
      case cfgMessages cfg of
        (msg : _) ->
          case runI (bindMessage ct msg) cfg of
            Left (ConsentViolation Transfer _ _ _) -> pure ()
            other -> expectationFailure ("expected Transfer violation at bind, got: " ++ show other)
        [] -> expectationFailure "missing message"

    it "resolved fetch with not-complyC times out to Err (not Ok)" $ do
      -- Future holds personal data, Sigma has no Collect, instant Ok is refused,
      -- timed step on timeout yields Err
      let e = EFetch (VLitFut "f0") 2 (VLitInt 99)
          obj =
            Object
              { objFields = Map.empty
              , objThread =
                  Running
                    RunThread
                      { rtExpr = e
                      , rtFut = "f_ret"
                      , rtAccClass = "Courier"
                      , rtTypedMeta = Nothing
                      }
              , objQueue = []
              , objClass = "Courier"
              }
          cfg0 =
            Config
              { cfgObjects = Map.singleton "o0" obj
              , cfgMessages = []
              , cfgFutures =
                  Map.singleton "f0" (Just (TaggedVal (VInt_ 7) tagAlice))
              , cfgConsent = Map.empty -- no Courier consent
              , cfgTime = 0
              , cfgFreshCtr = 0
              , cfgVarStore = Map.empty
              , cfgDefaultClass = "Courier"
              }
      -- Instant must not take Ok.
      case runI (stepInstant (error "unused") "o0" obj) cfg0 of
        Left NoRuleApplies -> pure ()
        Left (ConsentViolation {}) -> pure ()
        other -> expectationFailure ("expected no Ok reduction, got: " ++ show other)
      -- Timed timeout to Err
      case runI (stepTimed "o0" obj 2) cfg0 of
        Right (EVal (VErr (VLitInt 99)), _) -> pure ()
        other -> expectationFailure ("expected Err on timeout, got: " ++ show other)

  describe "typed activation" $ do
    it "NI: deliver-like thread blocked while renewCons runs on same user" $ do
      -- Running thread mutates alice, queued thread checks alice-> conflict.
      let cn =
            Set.fromList
              [ ACnstr Use (TA Set.empty (TagExpr (Set.singleton "u3") (Set.singleton "Delivery"))) Map.empty 0
              , ACnstr Collect (TA Set.empty (TagExpr (Set.singleton "u3") (Set.singleton "Delivery"))) Map.empty 0
              ]
          sigmaParams = Map.fromList [("u3", aliceTV)]
          tqe =
            TQE
              { tqeExpr = EVal VLitUnit
              , tqeFut = "f_d"
              , tqeAccClass = "Courier"
              , tqeParams = sigmaParams
              , tqeCn = cn
              , tqeUmVars = Set.empty
              , tqeDelta = Map.empty
              }
          -- Full Courier consent so InstCnstr alone would succeed.
          sig =
            foldr
              (\(a, e) s -> addConsent s "alice" "Courier" a "Delivery" e)
              Map.empty
              [(Use, 100), (Collect, 100), (Transfer, 100)]
          platRunning =
            Object
              { objFields = Map.empty
              , objThread =
                  Running
                    RunThread
                      { rtExpr = EVal VLitUnit
                      , rtFut = "f_r"
                      , rtAccClass = "Plat"
                      , rtTypedMeta = Just (TypedThreadMeta (Set.singleton "alice") Set.empty)
                      }
              , objQueue = []
              , objClass = "Plat"
              }
          courierIdle =
            Object
              { objFields = Map.empty
              , objThread = Idle
              , objQueue = [QTyped tqe]
              , objClass = "Courier"
              }
          cfg =
            Config
              { cfgObjects = Map.fromList [("plat", platRunning), ("cr", courierIdle)]
              , cfgMessages = []
              , cfgFutures = Map.fromList [("f_d", Nothing), ("f_r", Nothing)]
              , cfgConsent = sig
              , cfgTime = 0
              , cfgFreshCtr = 0
              , cfgVarStore = Map.empty
              , cfgDefaultClass = "Courier"
              }
      case runI (activateTyped "cr") cfg of
        Right (False, _) -> pure ()
        Right (True, _) -> expectationFailure "activation should be refused by NI"
        Left err -> expectationFailure ("unexpected error: " ++ show err)

    it "InstCnstr accepts via plcy(Delta) after in-method addCon" $ do
      let ct = either (error . show) id (inferMethodMeta (buildClassTable grantProg))
          (cn, _) = ctMethodMeta ct Map.! ("Demo", "grantThenUse")
          -- Empty Sigma: without plcy the Use/Collect constraints would fail.
          sigma = Map.fromList [("u", aliceTV), ("x", xTagged)]
          cfg =
            Config
              { cfgObjects = Map.singleton "d0" (Object Map.empty Idle [] "Demo")
              , cfgMessages = []
              , cfgFutures = Map.empty
              , cfgConsent = Map.empty
              , cfgTime = 0
              , cfgFreshCtr = 0
              , cfgVarStore = Map.empty
              , cfgDefaultClass = "Demo"
              }
      cn `shouldSatisfy` (not . Set.null)
      case runI (instCnstr cn Map.empty sigma "Demo") cfg of
        Right ((), _) -> pure ()
        Left err -> expectationFailure ("InstCnstr should succeed via plcy: " ++ show err)

    it "InstCnstr rejects when Sigma empty and method does not grant consent" $ do
      -- Same personal collect, but no addCon -> Delta has only PBase -> fail.
      let bareProg =
            Program
              { prgPurposes = ["Delivery"]
              , prgClasses =
                  [ ClassDecl
                      { cdName = "Demo"
                      , cdParams = []
                      , cdFields = []
                      , cdMethods =
                          [ MethodDecl TUnit TAEmpty "justUse" [(TUser, "u"), (TPersonal TInt, "x")] $
                              ELet "_z" (TPersonal TInt) (EVal (VVar "x")) (EVal VLitUnit)
                          ]
                      }
                  ]
              , prgMain = []
              }
          ct = either (error . show) id (inferMethodMeta (buildClassTable bareProg))
          (cn, _) = ctMethodMeta ct Map.! ("Demo", "justUse")
          sigma = Map.fromList [("u", aliceTV), ("x", xTagged)]
          cfg =
            Config
              { cfgObjects = Map.empty
              , cfgMessages = []
              , cfgFutures = Map.empty
              , cfgConsent = Map.empty
              , cfgTime = 0
              , cfgFreshCtr = 0
              , cfgVarStore = Map.empty
              , cfgDefaultClass = "Demo"
              }
      case runI (instCnstr cn Map.empty sigma "Demo") cfg of
        Left (ActivationFailed {}) -> pure ()
        other -> expectationFailure ("expected ActivationFailed, got: " ++ show other)
