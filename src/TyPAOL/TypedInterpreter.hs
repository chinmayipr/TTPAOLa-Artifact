{-# LANGUAGE LambdaCase #-}
module TyPAOL.TypedInterpreter where

import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List (delete)
import Data.Maybe (fromMaybe)
import Data.Foldable (foldl')
import Control.Monad (forM_, mapM, unless)
import TyPAOL.Consent (ConsentEntry (..), PolicyMap, RTag (..), actionAllowed, addConsent, tagCombine, tagUsers)
import TyPAOL.Eval
import TyPAOL.Interpreter
  ( InterpM
  , RuntimeError (..)
  , freshFutId
  , getObject
  , liftEval
  , updateCfg
  , modifyObject
  , putObject
  , valExprFromTaggedVal
  )
import TyPAOL.Runtime
import TyPAOL.Syntax
import TyPAOL.Types

extractUserId :: TaggedVal -> UserId
extractUserId (TaggedVal (VUserId_ u) _) = u
extractUserId _ = error "extractUserId: expected user value"


instAnn :: TagAnnotation -> Map FieldName TaggedVal -> Map VarName TaggedVal -> RTag
instAnn TAEmpty _ _ = RTagEmpty
instAnn (TA varRefs (TagExpr zs ps)) phi sigma =
  let lookupIn what m k =
        fromMaybe (error ("instAnn: unbound " ++ what ++ " " ++ k)) (Map.lookup k m)
      tags =
        [ tvTag (lookupIn "field" phi f) | RefField f <- Set.toList varRefs ]
          ++ [ tvTag (lookupIn "parameter" sigma x) | RefVar x <- Set.toList varRefs ]
      userIds =
        Set.fromList [extractUserId (lookupIn "user parameter" sigma z) | z <- Set.toList zs]
      combined = foldr tagCombine RTagEmpty tags
   in tagCombine combined (RTag userIds ps)
instAnn (TA _ TagEmpty) _ _ = RTagEmpty

-- Add a consent entry to a per-action policy map.
addToMap :: PolicyMap -> ClassName -> Action -> Purpose -> Int -> PolicyMap
addToMap pm cname act purpose absExp =
  Map.alter (Just . ins) act pm
 where
  newEntry = CE cname purpose absExp
  ins Nothing = Set.singleton newEntry
  ins (Just es) =
    let (same, _rest) = Set.partition (\e -> ceClass e == cname && cePurpose e == purpose) es
     in if Set.null same
          then Set.insert newEntry es
          else Set.insert newEntry (Set.difference es same)

plcy :: PolicyExpr -> PolicyMap -> Int -> PolicyMap
plcy PBase chi _ = chi
plcy (PAdd r cname act p dur) chi tau =
  addToMap (plcy r chi tau) cname act p (tau + dur)

instCnstr :: CnstrSet -> Map FieldName TaggedVal -> Map VarName TaggedVal -> ClassName -> ClassName -> DeltaEnv -> InterpM ()
instCnstr cn phi sigma clsAcc clsCallee deltaEnv = do
  sigmaBase <- gets cfgConsent
  tau <- gets cfgTime
  let applyDelta sig (u, r) =
        Map.alter
          (\mchi -> Just (plcy r (fromMaybe Map.empty mchi) tau))
          u
          sig
      sigma' =
        foldl'
          applyDelta
          sigmaBase
          [ (u, r)
          | (x, RTUser r) <- Map.toList deltaEnv
          , let u = extractUserId (sigma Map.! x)
          ]
  forM_ (Set.toList cn) $ \(ACnstr act ann _acDelta dur) -> do
    let tag = instAnn ann phi sigma
        cls = if act == Store then clsCallee else clsAcc
        ok = actionAllowed sigma' cls act tag (tau + dur)
    unless ok $ throwError (ActivationFailed act tag (tau + dur))

-- Typed instantaneous reduction: no per-action compliance checks (the
-- activation gate has already proved them).
stepInstantTyped :: ClassTable -> ObjId -> Object -> InterpM Expr
stepInstantTyped _ct oid obj = case objThread obj of
  Idle -> throwError NoRuleApplies
  Running rt -> go (rtExpr rt) rt
 where
  phi = objFields obj
  clsObj = objClass obj
  go :: Expr -> RunThread -> InterpM Expr
  go e rt = do
    case e of
      EAssign f ve -> do
        tv <- liftEval (evalVE phi ve)
        modifyObject oid (\o -> o {objFields = Map.insert f tv (objFields o)})
        pure (EVal VLitUnit)
      EAsyncCall ve m ves -> do
        tvCallee <- liftEval (evalVE phi ve)
        callee <- case tvCallee of
          TaggedVal (VObjId_ o) _ -> pure o
          _ -> throwError NoRuleApplies
        argTvs <- mapM (liftEval . evalVE phi) ves
        fut <- freshFutIdTyped
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
        TaggedVal vb _ <- liftEval (evalVE phi ve)
        case vb of
          VBool_ True -> pure e1
          VBool_ False -> pure e2
          _ -> throwError NoRuleApplies
      EMatch ve xv e1 yv e2 -> do
        tvScr <- liftEval (evalVE phi ve)
        case tvValue tvScr of
          VOk_ inner -> pure (substitute xv (valExprFromTaggedTyped inner) e1)
          VErr_ inner -> pure (substitute yv (valExprFromTaggedTyped inner) e2)
          _ -> throwError NoRuleApplies
      EAddCon ve pol -> do
        tvu <- liftEval (evalVE phi ve)
        u <- case tvu of
          TaggedVal (VUserId_ x) _ -> pure x
          _ -> throwError NoRuleApplies
        tau <- gets cfgTime
        let absExp = tau + polDuration pol
        updateCfg (\cfg -> cfg {cfgConsent = addConsent (cfgConsent cfg) u (polClass pol) (polAction pol) (polPurpose pol) absExp})
        pure (EVal VLitUnit)
      EFetch ve d veElse -> do
        tvf <- liftEval (evalVE phi ve)
        futId <- case tvf of
          TaggedVal (VFutId_ f) _ -> pure f
          _ -> throwError NoRuleApplies
        futMap <- gets cfgFutures
        case (Map.lookup futId futMap, d) of
          (Just (Just tvRes), _) -> pure (EVal (VOk (valExprFromTaggedTyped tvRes)))
          (Just Nothing, 0) -> do
            tvElse <- liftEval (evalVE phi veElse)
            pure (EVal (VErr (valExprFromTaggedTyped tvElse)))
          _ -> throwError NoRuleApplies
      EDelay 0 -> pure (EVal VLitUnit)
      EDelay _ -> throwError NoRuleApplies
      ELet x _ty (EVal ve) e2 -> do
        tv <- liftEval (evalVE phi ve)
        case tvValue tv of
          VFutId_ f -> pure (substitute x (VLitFut f) e2)
          _ -> pure (substitute x (valExprFromTaggedTyped tv) e2)
      ELet x ty e1 e2 -> do
        e1' <- stepInstantTyped _ct oid (obj {objThread = Running (rt {rtExpr = e1})})
        pure (ELet x ty e1' e2)
      EVal ve -> do
        tv <- liftEval (evalVE phi ve)
        let fut = rtFut rt
        updateCfg (\cfg -> cfg {cfgFutures = Map.insert fut (Just tv) (cfgFutures cfg)})
        modifyObject oid (\o -> o {objThread = Idle})
        pure (EVal VLitUnit)

valExprFromTaggedTyped :: TaggedVal -> ValExpr
valExprFromTaggedTyped = valExprFromTaggedVal

freshFutIdTyped :: InterpM FutId
freshFutIdTyped = freshFutId

getRunningThreadInfo :: InterpM [(ObjId, Set UserId, Set UserId)]
getRunningThreadInfo = do
  objs <- gets cfgObjects
  pure
    [ ( oid
      , maybe Set.empty ttmUm (rtTypedMeta rt)
      , maybe Set.empty ttmUc (rtTypedMeta rt)
      )
    | (oid, o) <- Map.toList objs
    , Running rt <- [objThread o]
    ]

tryInstCnstr ::
  CnstrSet ->
  Map FieldName TaggedVal ->
  Map VarName TaggedVal ->
  ClassName ->
  ClassName ->
  DeltaEnv ->
  InterpM (Either () ())
tryInstCnstr cn phi sigma clsAcc clsCallee dlt =
  catchError
    (Right <$> instCnstr cn phi sigma clsAcc clsCallee dlt)
    ( \case
        ActivationFailed _ _ _ -> pure (Left ())
        e -> throwError e
    )

activateTyped :: ObjId -> InterpM Bool
activateTyped oid = do
  obj <- getObject oid
  case objThread obj of
    Running _ -> pure False
    Idle ->
      let (pref, rest) = span isUntyped (objQueue obj)
       in case rest of
            (QTyped tqe : suf) -> do
              let phi = objFields obj
                  sigma = tqeParams tqe
              res <-
                tryInstCnstr
                  (tqeCn tqe)
                  phi
                  sigma
                  (tqeAccClass tqe)
                  (objClass obj)
                  (tqeDelta tqe)
              case res of
                Left () -> pure False
                Right () -> do
                  let um = Set.map (\x -> extractUserId (sigma Map.! x)) (tqeUmVars tqe)
                      uc =
                        Set.unions
                          [ tagUsers (instAnn ann phi sigma)
                          | ACnstr _ ann _ _ <- Set.toList (tqeCn tqe)
                          ]
                  running <- getRunningThreadInfo
                  let noConflict =
                        all
                          ( \( _, um', uc') ->
                              Set.null (Set.intersection um um')
                                && Set.null (Set.intersection um uc')
                                && Set.null (Set.intersection um' uc)
                          )
                          running
                  if noConflict
                    then do
                      let rt =
                            RunThread
                              { rtExpr = tqeExpr tqe
                              , rtFut = tqeFut tqe
                              , rtAccClass = tqeAccClass tqe
                              , rtTypedMeta = Just (TypedThreadMeta um uc)
                              }
                      putObject oid (obj {objThread = Running rt, objQueue = pref ++ suf})
                      pure True
                    else pure False
            _ -> pure False
 where
  isUntyped (QUntyped _) = True
  isUntyped _ = False

bindMessageTyped :: ClassTable -> Message -> InterpM ()
bindMessageTyped ct msg = do
  let oid = msgCallee msg
      mth = msgMethod msg
  obj <- getObject oid
  let cname = objClass obj
  (params, body0) <-
    maybe (throwError (StuckConfig "missing method body")) pure $
      Map.lookup (cname, mth) (ctMBody ct)
  (cn0, um0) <-
    maybe (throwError (StuckConfig "missing typed method metadata")) pure $
      Map.lookup (cname, mth) (ctMethodMeta ct)
  unless (length params == length (msgArgs msg)) $
    throwError (StuckConfig "arity mismatch")
  let sigma0 =
        Map.fromList
          [ (p, tv)
          | (p, tv) <- zip params (msgArgs msg)
          ]
      body =
        foldr
          (\(p, tv) acc -> substitute p (valExprFromTaggedTyped tv) acc)
          body0
          (zip params (msgArgs msg))
      tqe =
        TQE
          { tqeExpr = body
          , tqeFut = msgFut msg
          , tqeAccClass = cname
          , tqeParams = sigma0
          , tqeCn = cn0
          , tqeUmVars = um0
          , tqeDelta = Map.empty
          }
  updateCfg (\cfg -> cfg {cfgMessages = delete msg (cfgMessages cfg)})
  modifyObject oid (\o -> o {objQueue = objQueue o ++ [QTyped tqe]})
