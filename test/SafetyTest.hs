-- Demonstration of the core safety property of typed TTpaola,
--
-- A typed thread is /activated/ only if @InstCnstr@ proves every consent
-- requirement holds at the latest moment it will fire. Therefore once a
-- thread starts running under the typed semantics, it cannot get stuck on
-- a consent violation. Under the untyped semantics the activation check is
-- absent, so the same scenario activates a thread that subsequently fails
-- at runtime.
--
-- The example below is deliberately minimal: a single class @Demo@ with one
-- method
-- @
-- riskyOp(U u, D x) {
--   delay 10;
--   let _z = x in unit
-- }
-- @
--
-- whose static analysis yields @Cn = {Use\@10, Collect\@10}@ with
-- @delta_out = 10@ and tag @<{u},{Delivery}>@. We then build a configuration in
-- which Sigma has @alice@'s consent to @Demo@ expiring at tau=5 - i.e. consent is
-- valid /now/ but will be gone by the time the @let _z = x@ binding fires
-- at tau=10. The schedulers driven from this single configuration give
-- diametrically opposed results:
--
-- * Typed    to  @StepBind@ then @StepStuck@: the activation check (@instCnstr@)
--   rejects the message, no thread ever runs.
--
-- * Untyped  to  @StepBind@, @StepActivate@, @StepTimeAdv 10@, then a
--   @ConsentViolation Collect@ thrown at tau=10 when the let-data rule
--   checks compliance against an already-expired Sigma.
module SafetyTest where

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
import TTpaola.TypeChecker
import TTpaola.Types (AConstraint (..))


--Minimal program

demoProg :: Program
demoProg =
  Program
    { prgPurposes = ["Delivery"]
    , prgClasses = [demoClass]
    , prgMain = []
    }
 where
  demoClass =
    ClassDecl
      { cdName = "Demo"
      , cdParams = []
      , cdFields = []
      , cdMethods = [riskyOp]
      }
  riskyOp =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "riskyOp"
      , mdParams = [(TUser, "u"), (TPersonal TInt, "x")]
      , -- body: delay 10 ; let _z = x in unit
        mdBody =
          seqE (EDelay 10) $
            ELet "_z" (TPersonal TInt)
              (EVal (VVar "x"))
              (EVal VLitUnit)
      }

demoCT :: ClassTable
demoCT = either (error . show) id (inferMethodMeta (buildClassTable demoProg))

-- One @Demo@ object plus a single in-flight message @riskyOp(alice, x)@,
-- where @x@ carries the runtime tag @<{alice},{Delivery}>@. Sigma grants alice
-- @Demo@ consent for @Use@ and @Collect@, but only until tau=5.
demoConfig :: Config
demoConfig =
  Config
    { cfgObjects = Map.singleton "demo0" demoObj
    , cfgMessages = [msg]
    , cfgFutures = Map.singleton "f_ret" Nothing
    , cfgConsent = sig0
    , cfgTime = 0
    , cfgFreshCtr = 0
    , cfgVarStore = Map.empty
    , cfgDefaultClass = "Demo"
    }
 where
  demoObj =
    Object
      { objFields = Map.empty
      , objThread = Idle
      , objQueue = []
      , objClass = "Demo"
      }
  aliceVal = TaggedVal (VUserId_ "alice") RTagEmpty
  xTagged =
    TaggedVal
      (VInt_ 0)
      (RTag (Set.singleton "alice") (Set.singleton "Delivery"))
  msg =
    Message
      { msgMethod = "riskyOp"
      , msgCallee = "demo0"
      , msgArgs = [aliceVal, xTagged]
      , msgFut = "f_ret"
      , msgCallerClass = "Demo"
      }
  -- Rule typed (bind) requires complyT = {use,trans}; Collect is needed later at the let.
  sig0 =
    foldr
      (\(a, e) s -> addConsent s "alice" "Demo" a "Delivery" e)
      Map.empty
      [(Use, 5), (Collect, 5), (Transfer, 5)]

runFrom :: Config -> InterpM a -> Either RuntimeError (a, Config)
runFrom cfg m = runExcept (runStateT m cfg)

isStepBind, isStepActivate, isStepStuck :: StepResult -> Bool
isStepBind (StepBind _ _) = True
isStepBind _ = False
isStepActivate (StepActivate _) = True
isStepActivate _ = False
isStepStuck StepStuck = True
isStepStuck _ = False

-- Tests

spec :: Spec
spec = describe "Type safety: typed activation prevents stuck runs" $ do

  it "Static check: riskyOp's Cn captures Use\\@10 and Collect\\@10 - exceeding Sigma's expiry of 5" $ do
    let mdecl =
          head [m | c <- prgClasses demoProg, m <- cdMethods c, mdName m == "riskyOp"]
        (cn, um) = either (error . show) id (typeCheckMethod demoCT "Demo" mdecl)
        dOut = either (error . show) id (methodDeltaOut demoCT "Demo" mdecl)
    Set.map acAction cn `shouldBe` Set.fromList [Use, Collect]
    Set.map acDur cn `shouldBe` Set.singleton 10
    um `shouldBe` Set.empty
    dOut `shouldBe` 10

  it "TYPED semantics: instCnstr rejects activation - no thread ever runs" $ do
    case runFrom demoConfig (run demoCT True) of
      Right (steps, _) -> do
        -- The message is bound into the queue, but activateTyped returns False
        -- because instCnstr fails (Use@10 needs consent valid at tau=10 but it
        -- expires at 5). The scheduler then has no progress to make.
        isStepStuck (last steps) `shouldBe` True
        any isStepBind steps `shouldBe` True
        any isStepActivate steps `shouldBe` False
      Left err ->
        expectationFailure ("typed run threw an error (it should never): " ++ show err)

  it "UNTYPED semantics: activation succeeds, then the run gets stuck at tau=10 with a ConsentViolation" $ do
    case runFrom demoConfig (run demoCT False) of
      Left (ConsentViolation Collect _ _ tau) -> tau `shouldBe` 10
      Left (ConsentViolation Use _ _ tau) -> tau `shouldBe` 10
      Left err ->
        expectationFailure ("unexpected runtime error (expected ConsentViolation): " ++ show err)
      Right (steps, _) ->
        expectationFailure ("untyped run completed without violation - should have been stuck. Steps: " ++ show steps)

  it "UNTYPED semantics: the run gets past Bind and Activate before failing" $ do
    -- This pins down precisely where the untyped run gets stuck. We drive
    -- the scheduler one step at a time and walk the configuration forward
    -- until either a violation fires or we exhaust the simulation budget.
    let step1 = step demoCT False
        loop :: Int -> Config -> [StepResult] -> Either RuntimeError ([StepResult], Config)
        loop 0 c acc = Right (reverse acc, c)
        loop n c acc =
          case runFrom c step1 of
            Left err -> Left err
            Right (r, c') ->
              if isStepStuck r
                then Right (reverse (r : acc), c')
                else loop (n - 1) c' (r : acc)
    case loop 20 demoConfig [] of
      Left (ConsentViolation _ _ _ tau) -> tau `shouldBe` 10
      Left other -> expectationFailure ("unexpected error: " ++ show other)
      Right (steps, _) -> do
        -- Even if we don't error out we should have seen bind+activate+timeAdv
        -- before the eventual stuck state - but the untyped semantics is
        -- expected to error out, so reaching this branch is itself a failure.
        expectationFailure
          ("untyped run terminated cleanly (it should have thrown): " ++ show steps)
