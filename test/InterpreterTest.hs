{-# LANGUAGE LambdaCase #-}
-- Operational tests for the fetch timeout behaviour
module InterpreterTest where

import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Hspec

import TTpaola.Consent
import TTpaola.Interpreter
import TTpaola.Runtime
import TTpaola.Scheduler
import TTpaola.Syntax
import TTpaola.TypeChecker (inferMethodMeta)

-- Build a minimal config containing an object that runs the expression we
-- want to step, plus an unresolved future f0.
mkConfig :: Expr -> Config
mkConfig e =
  Config
    { cfgObjects =
        Map.singleton "o0" $
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
    , cfgMessages = []
    , cfgFutures = Map.singleton "f0" Nothing
    , cfgConsent = sigmaForCourier
    , cfgTime = 0
    , cfgFreshCtr = 0
    , cfgVarStore = Map.empty
    , cfgDefaultClass = "Courier"
    }

sigmaForCourier :: ConsentEnv
sigmaForCourier =
  foldr
    (\(c, a, p, e) sig -> addConsent sig "alice" c a p e)
    Map.empty
    [ ("Courier", Use,      "Delivery", 100)
    , ("Courier", Collect,  "Delivery", 100)
    , ("Courier", Transfer, "Delivery", 100)
    ]

runStep :: InterpM a -> Config -> Either RuntimeError (a, Config)
runStep m cfg = runExcept (runStateT m cfg)

spec :: Spec
spec = describe "TTpaola.Interpreter" $ do

  describe "#13 fetch with d > 0: timed step decrements delta" $ do
    it "fetch(f0)^4 with Delta=1 reduces to fetch(f0)^3" $ do
      let e = EFetch (VLitFut "f0") 4 (VLitInt 0)
          cfg = mkConfig e
      case runStep (stepTimed "o0" (cfgObjects cfg Map.! "o0") 1) cfg of
        Right (EFetch _ d _, _) -> d `shouldBe` 3
        other -> expectationFailure ("unexpected result: " ++ show other)

  describe "#13 fetch when future is resolved before timeout" $ do
    it "instant step turns fetch into Ok(value)" $ do
      let e = EFetch (VLitFut "f0") 4 (VLitInt 0)
          cfg0 = mkConfig e
          cfg = cfg0 {cfgFutures = Map.singleton "f0" (Just (TaggedVal (VInt_ 42) RTagEmpty))}
      case runStep (stepInstant undefined "o0" (cfgObjects cfg Map.! "o0")) cfg of
        Right (EVal (VOk _), _) -> pure ()
        other -> expectationFailure ("unexpected result: " ++ show other)

  describe "#14 fetch timeout: when delta' >= delta and future unresolved  to  Err branch" $ do
    it "stepTimed with delta' = 4 on fetch^4 returns Err(default)" $ do
      let e = EFetch (VLitFut "f0") 4 (VLitInt 99)
          cfg = mkConfig e
      case runStep (stepTimed "o0" (cfgObjects cfg Map.! "o0") 4) cfg of
        Right (EVal (VErr (VLitInt 99)), _) -> pure ()
        other -> expectationFailure ("unexpected result: " ++ show other)

  describe "delay delta as a leaf" $ do
    it "stepTimed on delay 5 with Delta=2 reduces to delay 3" $ do
      let e = EDelay 5
          cfg = mkConfig e
      case runStep (stepTimed "o0" (cfgObjects cfg Map.! "o0") 2) cfg of
        Right (EDelay d, _) -> d `shouldBe` 3
        other -> expectationFailure ("unexpected: " ++ show other)
    it "stepTimed on delay 5 with Delta=5 reduces to unit (no continuation)" $ do
      let e = EDelay 5
          cfg = mkConfig e
      case runStep (stepTimed "o0" (cfgObjects cfg Map.! "o0") 5) cfg of
        Right (EVal VLitUnit, _) -> pure ()
        other -> expectationFailure ("unexpected: " ++ show other)
    it "stepInstant on delay 0 reduces to unit" $ do
      let e = EDelay 0
          cfg = mkConfig e
      case runStep (stepInstant undefined "o0" (cfgObjects cfg Map.! "o0")) cfg of
        Right (EVal VLitUnit, _) -> pure ()
        other -> expectationFailure ("unexpected: " ++ show other)
    it "delay delta ; e2  steps to e2 once the delay has elapsed" $ do
      let inner = EVal (VLitInt 7)
          e = ELet "_" TUnit (EDelay 3) inner
          cfg = mkConfig e
      -- One timed step of size 3 elapses the delay
      case runStep (stepTimed "o0" (cfgObjects cfg Map.! "o0") 3) cfg of
        Right (ELet _ _ (EVal VLitUnit) _, _) -> pure ()
        other -> expectationFailure ("unexpected: " ++ show other)

  describe "fetch^0 on an unresolved future" $ do
    it "instant step takes the Err branch immediately" $ do
      let e = EFetch (VLitFut "f0") 0 (VLitInt 9)
          cfg = mkConfig e
      case runStep (stepInstant undefined "o0" (cfgObjects cfg Map.! "o0")) cfg of
        Right (EVal (VErr (VLitInt 9)), _) -> pure ()
        other -> expectationFailure ("unexpected: " ++ show other)

  describe "scheduler end-to-end (regression: object state must survive steps)" $ do
    -- A method that assigns to a field and returns a value. Driving it
    -- through the full scheduler loop checks that (a) the field update is
    -- not clobbered by a stale object snapshot, (b) the thread goes Idle
    -- exactly once and stays Idle, and (c) the future holds the real
    -- return value, not unit.
    let storeProg =
          Program
            { prgPurposes = ["Delivery"]
            , prgClasses =
                [ ClassDecl
                    { cdName = "Store"
                    , cdParams = []
                    , cdFields = [(TInt, "slot")]
                    , cdMethods =
                        [ MethodDecl
                            { mdRetType = TInt
                            , mdRetAnn = TAEmpty
                            , mdName = "put"
                            , mdParams = [(TInt, "a")]
                            , mdBody =
                                ELet "_k" TUnit (EAssign "slot" (VVar "a")) $
                                  EVal (VLitInt 42)
                            }
                        ]
                    }
                ]
            , prgMain = []
            }
        storeCT = either (error . show) id (inferMethodMeta (buildClassTable storeProg))
        storeCfg =
          Config
            { cfgObjects =
                Map.singleton "s0" $
                  Object
                    { objFields = Map.singleton "slot" (TaggedVal (VInt_ 0) RTagEmpty)
                    , objThread = Idle
                    , objQueue = []
                    , objClass = "Store"
                    }
            , cfgMessages =
                [ Message
                    { msgMethod = "put"
                    , msgCallee = "s0"
                    , msgArgs = [TaggedVal (VInt_ 5) RTagEmpty]
                    , msgFut = "f_ret"
                    , msgCallerClass = "Store"
                    }
                ]
            , cfgFutures = Map.singleton "f_ret" Nothing
            , cfgConsent = Map.empty
            , cfgTime = 0
            , cfgFreshCtr = 0
            , cfgVarStore = Map.empty
            , cfgDefaultClass = "Store"
            }
        -- Bounded driver: terminates the test even if the scheduler
        -- livelocks (which is exactly the failure mode being guarded).
        runBounded :: Bool -> Either RuntimeError ([StepResult], Config)
        runBounded typed = go (50 :: Int) storeCfg []
         where
          go 0 c acc = Right (reverse acc, c)
          go n c acc =
            case runStep (step storeCT typed) c of
              Left err -> Left err
              Right (StepStuck, c') -> Right (reverse (StepStuck : acc), c')
              Right (r, c') -> go (n - 1) c' (r : acc)
        checkFinal :: Either RuntimeError ([StepResult], Config) -> Expectation
        checkFinal = \case
          Left err -> expectationFailure ("runtime error: " ++ show err)
          Right (steps, cfgEnd) -> do
            -- Must terminate (reach StepStuck) within the budget.
            case reverse steps of
              (StepStuck : _) -> pure ()
              _ -> expectationFailure ("did not terminate: " ++ show steps)
            -- Field update must have survived.
            let obj = cfgObjects cfgEnd Map.! "s0"
            Map.lookup "slot" (objFields obj)
              `shouldBe` Just (TaggedVal (VInt_ 5) RTagEmpty)
            -- Thread must have ended Idle.
            case objThread obj of
              Idle -> pure ()
              Running _ -> expectationFailure "thread still running after return"
            -- Future must hold the real return value, not unit.
            Map.lookup "f_ret" (cfgFutures cfgEnd)
              `shouldBe` Just (Just (TaggedVal (VInt_ 42) RTagEmpty))
    it "untyped: assignment persists, future resolved, thread Idle, run terminates" $
      checkFinal (runBounded False)
    it "typed: assignment persists, future resolved, thread Idle, run terminates" $
      checkFinal (runBounded True)
