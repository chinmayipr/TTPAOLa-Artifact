{-# LANGUAGE LambdaCase #-}
module TyPAOL.Interpreter where

import Control.Monad (forM_, mapM, unless, when)
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.List (delete)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import TyPAOL.Consent
import TyPAOL.Eval
import TyPAOL.Runtime
import TyPAOL.Syntax

data RuntimeError
  = ConsentViolation Action ClassName RTag Int
  | ActivationFailed Action RTag Int
  | NoRuleApplies
  | NoTimedStep
  | NoProgress
  | StuckConfig String
  | EvalFailed EvalError
  deriving (Show)

type InterpM a = StateT Config (Except RuntimeError) a

liftEval :: Either EvalError a -> InterpM a
liftEval = either (throwError . EvalFailed) pure

valExprFromTaggedVal :: TaggedVal -> ValExpr
valExprFromTaggedVal (TaggedVal v t) = go v
 where
  go :: Value -> ValExpr
  go (VInt_ n) = wrap (VLitInt n)
  go (VBool_ b) = wrap (VLitBool b)
  go VUnit_ = wrap VLitUnit
  go (VUserId_ u) = wrap (VLitUser u)
  go (VObjId_ o) = wrap (VLitObj o)
  go (VFutId_ f) = wrap (VLitFut f)
  go (VOk_ tv) = wrap (VOk (valExprFromTaggedVal tv))
  go (VErr_ tv) = wrap (VErr (valExprFromTaggedVal tv))
  wrap inner = case t of
    RTagEmpty -> inner
    rt -> VTag inner (runtimeTagToSource rt)

runtimeTagToSource :: RTag -> Tag
runtimeTagToSource RTagEmpty = TagEmpty
runtimeTagToSource (RTag us ps) = TagExpr us ps

updateCfg :: (Config -> Config) -> InterpM ()
updateCfg f = state (\s -> ((), f s))

modifyObject :: ObjId -> (Object -> Object) -> InterpM ()
modifyObject oid f = do
  objs <- gets cfgObjects
  o <- maybe (throwError (StuckConfig ("no object " ++ oid))) pure (Map.lookup oid objs)
  updateCfg (\cfg -> cfg {cfgObjects = Map.insert oid (f o) objs})

getObject :: ObjId -> InterpM Object
getObject oid = do
  objs <- gets cfgObjects
  maybe (throwError (StuckConfig ("no object " ++ oid))) pure (Map.lookup oid objs)

putObject :: ObjId -> Object -> InterpM ()
putObject oid o =
  updateCfg (\cfg -> cfg {cfgObjects = Map.insert oid o (cfgObjects cfg)})

freshFutId :: InterpM FutId
freshFutId = do
  n <- gets cfgFreshCtr
  updateCfg (\cfg -> cfg {cfgFreshCtr = n + 1})
  pure ("fut_" ++ show n)

-- Instantaneous reduction (untyped), with per-action comply checks.
stepInstant :: ClassTable -> ObjId -> Object -> InterpM Expr
stepInstant _ct oid obj = case objThread obj of
  Idle -> throwError NoRuleApplies
  Running rt -> go (rtExpr rt) rt
 where
  phi = objFields obj
  clsObj = objClass obj
  go :: Expr -> RunThread -> InterpM Expr
  go e rt = do
    sig <- gets cfgConsent
    tau <- gets cfgTime
    let clsCaller = rtAccClass rt
    case e of
      EAssign f ve -> do
        tv <- liftEval (evalVE phi ve)
        unless (complyS sig clsObj clsCaller (tvTag tv) tau) $
          throwError (ConsentViolation Store clsObj (tvTag tv) tau)
        modifyObject oid (\o -> o {objFields = Map.insert f tv (objFields o)})
        pure (EVal VLitUnit)
      EAsyncCall ve m ves -> do
        tvCallee <- liftEval (evalVE phi ve)
        callee <- case tvCallee of
          TaggedVal (VObjId_ o) _ -> pure o
          _ -> throwError NoRuleApplies
        argTvs <- mapM (liftEval . evalVE phi) ves
        forM_
          argTvs
          ( \tv ->
              unless (complyT sig clsObj (tvTag tv) tau) $
                throwError (ConsentViolation Transfer clsObj (tvTag tv) tau)
          )
        fut <- freshFutId
        let msg =
              Message
                { msgMethod = m
                , msgCallee = callee
                , msgArgs = argTvs
                , msgFut = fut
                , msgCallerClass = clsObj
                }
        updateCfg (\cfg -> cfg {cfgMessages = cfgMessages cfg ++ [msg], cfgFutures = Map.insert fut Nothing (cfgFutures cfg)})
        pure (EVal (VLitFut fut))
      EIf ve e1 e2 -> do
        TaggedVal vb tv <- liftEval (evalVE phi ve)
        case vb of
          VBool_ True -> do
            unless (complyU sig clsCaller tv tau) $
              throwError (ConsentViolation Use clsCaller tv tau)
            pure e1
          VBool_ False -> do
            unless (complyU sig clsCaller tv tau) $
              throwError (ConsentViolation Use clsCaller tv tau)
            pure e2
          _ -> throwError NoRuleApplies
      EMatch ve xv e1 yv e2 -> do
        tvScr <- liftEval (evalVE phi ve)
        case tvValue tvScr of
          VOk_ inner -> do
            unless (complyU sig clsCaller (tvTag tvScr) tau) $
              throwError (ConsentViolation Use clsCaller (tvTag tvScr) tau)
            pure (substitute xv (valExprFromTaggedVal inner) e1)
          VErr_ inner -> do
            unless (complyU sig clsCaller (tvTag tvScr) tau) $
              throwError (ConsentViolation Use clsCaller (tvTag tvScr) tau)
            pure (substitute yv (valExprFromTaggedVal inner) e2)
          _ -> throwError NoRuleApplies
      EAddCon ve pol -> do
        tvu <- liftEval (evalVE phi ve)
        u <- case tvu of
          TaggedVal (VUserId_ x) _ -> pure x
          _ -> throwError NoRuleApplies
        let absExp = tau + polDuration pol
        updateCfg (\cfg -> cfg {cfgConsent = addConsent (cfgConsent cfg) u (polClass pol) (polAction pol) (polPurpose pol) absExp})
        pure (EVal VLitUnit)
      EFetch ve d veElse -> do
        tvf <- liftEval (evalVE phi ve)
        (futId, tv) <- case tvf of
          TaggedVal (VFutId_ f) tg -> pure (f, tg)
          _ -> throwError NoRuleApplies
        unless (complyU sig clsCaller tv tau) $
          throwError (ConsentViolation Use clsCaller tv tau)
        futMap <- gets cfgFutures
        case (Map.lookup futId futMap, d) of
          (Just (Just tvRes), _) ->
            pure (EVal (VOk (valExprFromTaggedVal tvRes)))
          -- Timeout already elapsed and still unresolved: take the Err branch
          -- now, since waitTime is 0 and no timed step would fire.
          (Just Nothing, 0) -> do
            tvElse <- liftEval (evalVE phi veElse)
            pure (EVal (VErr (valExprFromTaggedVal tvElse)))
          _ -> throwError NoRuleApplies
      EDelay 0 -> pure (EVal VLitUnit)
      EDelay _ -> throwError NoRuleApplies
      ELet x _ty (EVal ve) e2 -> do
        tv <- liftEval (evalVE phi ve)
        case tvValue tv of
          VFutId_ f -> pure (substitute x (VLitFut f) e2)
          _ -> do
            unless (complyC sig clsCaller (tvTag tv) tau) $
              throwError (ConsentViolation Collect clsCaller (tvTag tv) tau)
            pure (substitute x (valExprFromTaggedVal tv) e2)
      ELet x ty e1 e2 -> do
        e1' <- stepInstant _ct oid (obj {objThread = Running (rt {rtExpr = e1})})
        pure (ELet x ty e1' e2)
      EVal ve -> do
        tv <- liftEval (evalVE phi ve)
        unless (complyT sig clsCaller (tvTag tv) tau) $
          throwError (ConsentViolation Transfer clsCaller (tvTag tv) tau)
        let fut = rtFut rt
        updateCfg (\cfg -> cfg {cfgFutures = Map.insert fut (Just tv) (cfgFutures cfg)})
        modifyObject oid (\o -> o {objThread = Idle})
        pure (EVal VLitUnit)

-- Timed reduction by delta time units.
stepTimed :: ObjId -> Object -> Duration -> InterpM Expr
stepTimed oid obj delta = case objThread obj of
  Idle -> throwError NoTimedStep
  Running rt -> go (rtExpr rt) rt
 where
  phi = objFields obj
  go :: Expr -> RunThread -> InterpM Expr
  go e rt = case e of
    EDelay d
      | d > delta -> pure (EDelay (d - delta))
      | otherwise -> pure (EVal VLitUnit)
    EFetch ve d veElse
      | d > delta -> pure (EFetch ve (d - delta) veElse)
      | otherwise -> do
          tvf <- liftEval (evalVE phi ve)
          futId <- case tvf of
            TaggedVal (VFutId_ f) _ -> pure f
            _ -> throwError NoTimedStep
          futMap <- gets cfgFutures
          case Map.lookup futId futMap of
            Just Nothing -> do
              tvElse <- liftEval (evalVE phi veElse)
              pure (EVal (VErr (valExprFromTaggedVal tvElse)))
            _ -> throwError NoTimedStep
    ELet x ty e1 e2 -> do
      e1' <- stepTimed oid (obj {objThread = Running (rt {rtExpr = e1})}) delta
      pure (ELet x ty e1' e2)
    _ -> throwError NoTimedStep

waitTime :: Expr -> Duration
waitTime (EFetch _ d _) = d
waitTime (EDelay d) = d
waitTime (ELet _ _ e1 _) = waitTime e1
waitTime _ = 0

-- Global time advancement.
timeAdv :: InterpM ()
timeAdv = do
  objs <- gets cfgObjects
  let runners =
        [ (oid, o, rt, w)
        | (oid, o) <- Map.toList objs
        , Running rt <- [objThread o]
        , let w = waitTime (rtExpr rt)
        , w > 0
        ]
  when (null runners) (throwError NoProgress)
  let dmin = minimum (map (\(_, _, _, w) -> w) runners)
  forM_ runners $ \(oid, o, rt, _) -> do
    eNew <- stepTimed oid o dmin
    let rt' = rt {rtExpr = eNew}
    putObject oid (o {objThread = Running rt'})
  tau0 <- gets cfgTime
  let tau1 = tau0 + dmin
  sig <- gets cfgConsent
  updateCfg (\cfg -> cfg {cfgTime = tau1, cfgConsent = remExpired sig tau1})

bindMessage :: ClassTable -> Message -> InterpM ()
bindMessage ct msg = do
  let oid = msgCallee msg
      mth = msgMethod msg
  obj <- getObject oid
  let cname = objClass obj
  (params, body0) <-
    maybe (throwError (StuckConfig "missing method body")) pure $
      Map.lookup (cname, mth) (ctMBody ct)
  unless (length params == length (msgArgs msg)) $
    throwError (StuckConfig "arity mismatch")
  let body =
        foldr
          (\(p, tv) acc -> substitute p (valExprFromTaggedVal tv) acc)
          body0
          (zip params (msgArgs msg))
  let qe =
        QueueEntry
          { qeExpr = body
          , qeFut = msgFut msg
          , qeAccClass = cname -- accountable class is the callee's class
          }
  updateCfg (\cfg -> cfg {cfgMessages = delete msg (cfgMessages cfg)})
  modifyObject oid (\o -> o {objQueue = objQueue o ++ [QUntyped qe]})

-- Activation (untyped): no constraint gate, just start the next thread.
activateUntyped :: ObjId -> InterpM Bool
activateUntyped oid = do
  obj <- getObject oid
  case objThread obj of
    Running _ -> pure False
    Idle ->
      let (pref, rest) = span isTyped (objQueue obj)
       in case rest of
            (QUntyped qe : suf) -> do
              let rt =
                    RunThread
                      { rtExpr = qeExpr qe
                      , rtFut = qeFut qe
                      , rtAccClass = qeAccClass qe
                      , rtTypedMeta = Nothing
                      }
              putObject oid (obj {objThread = Running rt, objQueue = pref ++ suf})
              pure True
            _ -> pure False
 where
  isTyped (QTyped _) = True
  isTyped _ = False
