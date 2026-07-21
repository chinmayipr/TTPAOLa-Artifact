{-# LANGUAGE LambdaCase #-}
module TTpaola.TypeChecker where

import Control.Monad.Except
import Control.Monad (forM, unless)
import Control.Monad.State.Strict
import Data.List (find)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Set (Set)
import TTpaola.Runtime (ClassTable (..))
import TTpaola.Syntax
import TTpaola.Types

data TypeError = TypeError String deriving (Show)

data CheckerState = CheckerState
  { csGamma :: GammaEnv
  , csDelta :: DeltaEnv
  , csDur :: Duration
  , csFresh :: Int
  , csPurposes :: Set Purpose
  , csClass :: ClassName
  }
  deriving (Show)

type CheckM a = StateT CheckerState (Except TypeError) a

throwTy :: String -> CheckM a
throwTy = throwError . TypeError

cnstrU :: TagAnnotation -> DeltaEnv -> Duration -> CnstrSet
cnstrU TAEmpty _ _ = Set.empty
cnstrU ann delta dur = Set.singleton (ACnstr Use ann delta dur)

cnstrC :: TagAnnotation -> DeltaEnv -> Duration -> CnstrSet
cnstrC TAEmpty _ _ = Set.empty
cnstrC ann delta dur = cnstrU ann delta dur <> Set.singleton (ACnstr Collect ann delta dur)

cnstrT :: TagAnnotation -> DeltaEnv -> Duration -> CnstrSet
cnstrT TAEmpty _ _ = Set.empty
cnstrT ann delta dur = cnstrU ann delta dur <> Set.singleton (ACnstr Transfer ann delta dur)

cnstrS :: TagAnnotation -> DeltaEnv -> Duration -> CnstrSet
cnstrS TAEmpty _ _ = Set.empty
cnstrS ann delta dur = cnstrC ann delta dur <> Set.singleton (ACnstr Store ann delta dur)

lookupClass :: ClassTable -> ClassName -> ClassDecl
lookupClass ct nm =
  maybe (error ("Unknown class: " ++ nm)) id (Map.lookup nm (ctClasses ct))

baseFromRes :: ExtType -> Type
baseFromRes (DTRes bt _) = bt
baseFromRes (DTBase bt _) = bt
baseFromRes _ = TInt

asSimpleBase :: ExtType -> Type
asSimpleBase (DTBase bt _) = bt
asSimpleBase _ = TUnit

-- Substitute a parameter name with the caller's argument expression inside a
-- tag annotation. This is used when typing async-call return annotations so
-- that variable references survive across the call boundary.
-- Only the VVar and VLitUser argument forms produce a renaming, other
-- argument forms leave the annotation unchanged.
substAnnVar :: VarName -> ValExpr -> TagAnnotation -> TagAnnotation
substAnnVar _ _ TAEmpty = TAEmpty
substAnnVar pname argVe (TA vrs tg) = TA vrs (substTag pname argVe tg)

typeCheckValExpr :: ClassTable -> ValExpr -> CheckM (ExtType, CnstrSet)
typeCheckValExpr _ct = \case
  VLitInt _ -> pure (DTBase TInt TAEmpty, Set.empty)
  VLitBool _ -> pure (DTBase TBool TAEmpty, Set.empty)
  VLitUnit -> pure (DTBase TUnit TAEmpty, Set.empty)
  VLitUser _ -> pure (DTBase TUser TAEmpty, Set.empty)
  VLitObj _ -> throwTy "object literal not allowed in static typing"
  VLitFut _ -> throwTy "future literal not allowed in static typing"
  VVar x -> do
    g <- gets csGamma
    d <- gets csDelta
    case (Map.lookup x g, Map.lookup x d) of
      (Just et, _) -> pure (et, Set.empty)
      (_, Just et) -> pure (et, Set.empty)
      _ -> throwTy ("unknown variable " ++ x)
  VField f -> do
    g <- gets csGamma
    d <- gets csDelta
    case (Map.lookup f g, Map.lookup f d) of
      (Just et, _) -> pure (et, Set.empty)
      (_, Just et) -> pure (et, Set.empty)
      _ -> throwTy ("unknown field " ++ f)
  VThis -> throwTy "this not allowed as value expression in static typing"
  VOp op a b -> do
    (t1, c1) <- typeCheckValExpr _ct a
    (t2, c2) <- typeCheckValExpr _ct b
    case op of
      And -> unless (cmpTy TBool t1 && cmpTy TBool t2) (throwTy "boolean operands")
      Or -> unless (cmpTy TBool t1 && cmpTy TBool t2) (throwTy "boolean operands")
      Eq -> unless (cmpTy TInt t1 && cmpTy TInt t2) (throwTy "equality operands")
      Lt -> unless (cmpTy TInt t1 && cmpTy TInt t2) (throwTy "comparison operands")
      Gt -> unless (cmpTy TInt t1 && cmpTy TInt t2) (throwTy "comparison operands")
      _ -> unless (cmpTy TInt t1 && cmpTy TInt t2) (throwTy "arithmetic operands")
    let ret = case op of
          And -> TBool
          Or -> TBool
          Eq -> TBool
          Lt -> TBool
          Gt -> TBool
          _ -> TInt
        ann = taCompose (annotationOf t1) (annotationOf t2)
    pure (DTBase ret ann, c1 <> c2)
  VTag ve t -> do
    (et, c) <- typeCheckValExpr _ct ve
    let ann = TA Set.empty t
    pure (DTBase (baseFromRes et) (taCompose (annotationOf et) ann), c)
  VOk ve -> do
    (et, c) <- typeCheckValExpr _ct ve
    pure (DTRes (baseFromRes et) (annotationOf et), c)
  VErr ve -> do
    (et, c) <- typeCheckValExpr _ct ve
    pure (DTRes (baseFromRes et) (annotationOf et), c)

typeCheckExpr :: ClassTable -> Expr -> CheckM (ExtType, CnstrSet)
typeCheckExpr ct = \case
  EVal ve -> typeCheckValExpr ct ve
  EAssign f ve -> do
    g <- gets csGamma
    etF <- maybe (throwTy ("unknown assign field " ++ f)) pure (Map.lookup f g)
    (etV, cnV) <- typeCheckValExpr ct ve
    unless (cmpTy (asSimpleBase etF) etV) (throwTy "assignment type mismatch")
    d <- gets csDur
    delta <- gets csDelta
    let cn = cnstrS (annotationOf etV) delta d
    pure (DTBase TUnit TAEmpty, cnV <> cn)
  EAsyncCall ve m args -> do
    (et0, c0) <- typeCheckValExpr ct ve
    cname <- case et0 of
      RTClass c _ -> pure c
      _ -> throwTy "async callee not a class reference"
    (argTys, retTy, retAnn) <-
      maybe (throwTy "unknown method") pure $
        Map.lookup (cname, m) (ctMType ct)
    unless (length argTys == length args) (throwTy "async arity")
    -- Rule (async-call): distinct actuals for user-typed parameters (no aliasing).
    let userActuals =
          [ argVe
          | (TUser, argVe) <- zip argTys args
          ]
        userVars = [x | VVar x <- userActuals]
    unless (length userVars == length (Set.fromList userVars)) $
      throwTy "async call: aliased user actual parameters"
    unless (all (\a -> case a of VVar _ -> True; _ -> False) userActuals) $
      throwTy "async call: user actuals must be variables"
    -- Look up the method declaration to obtain parameter names so we can
    -- substitute them with the caller's argument variables in the return
    -- annotation.
    let cls = lookupClass ct cname
        mdeclMb = find (\md -> mdName md == m) (cdMethods cls)
    mdecl <- maybe (throwTy ("unknown method " ++ m)) pure mdeclMb
    d <- gets csDur
    delta <- gets csDelta
    cnParts <-
      forM (zip argTys args) $ \(argTy, argVe) -> do
        (etArg, cnA) <- typeCheckValExpr ct argVe
        unless (cmpTy argTy etArg) (throwTy "async arg type")
        let cnT = case argTy of TPersonal _ -> cnstrT (annotationOf etArg) delta d; _ -> Set.empty
        pure (cnA <> cnT)
    let cnArgs = mconcat cnParts
        retAnn' =
          foldr
            (\(paramName, argVe) ann -> substAnnVar paramName argVe ann)
            retAnn
            (zip (map snd (mdParams mdecl)) args)
    pure (RTFut retTy retAnn', c0 <> cnArgs)
  -- (t-delay)
  EDelay dur -> do
    modify (\s -> s {csDur = csDur s + dur})
    pure (DTBase TUnit TAEmpty, Set.empty)
  EFetch ve dur veElse -> do
    (etF, c0) <- typeCheckValExpr ct ve
    (lam, bt) <- case etF of
      RTFut b lam -> pure (lam, b)
      _ -> throwTy "fetch expects future"
    (etE, cE) <- typeCheckValExpr ct veElse
    unless (annotationOf etE == TAEmpty) (throwTy "fetch else annotation must be empty")
    unless (cmpTy bt etE) (throwTy "fetch else type mismatch")
    d0 <- gets csDur
    delta <- gets csDelta
    let cn = cnstrC lam delta (d0 + dur)
    modify (\s -> s {csDur = csDur s + dur})
    pure (DTRes bt lam, c0 <> cE <> cn)
  EIf ve e1 e2 -> do
    (tv, c0) <- typeCheckValExpr ct ve
    unless (cmpTy TBool tv) (throwTy "if guard")
    d0 <- gets csDur
    delta <- gets csDelta
    let cnG = cnstrU (annotationOf tv) delta d0
    st <- get
    (t1, cn1) <- typeCheckExpr ct e1
    d1 <- gets csDur
    put st
    (t2, cn2) <- typeCheckExpr ct e2
    d2 <- gets csDur
    put st {csDur = max d1 d2}
    unless (t1 == t2) (throwTy "if branches disagree (simplified)")
    pure (t1, c0 <> cn1 <> cn2 <> cnG)
  EMatch ve xv e1 yv e2 -> do
    (tv, c0) <- typeCheckValExpr ct ve
    lam <- case tv of
      DTRes _ l -> pure l
      _ -> throwTy "match expects result type"
    d0 <- gets csDur
    delta <- gets csDelta
    let cnG = cnstrU lam delta d0
        ext = DTBase (baseFromRes tv) lam
    st <- get
    let g0 = csGamma st
    put st {csGamma = Map.insert xv ext g0}
    (t1, cn1) <- typeCheckExpr ct e1
    d1 <- gets csDur
    put st {csGamma = Map.insert yv ext g0, csDur = csDur st}
    (t2, cn2) <- typeCheckExpr ct e2
    d2 <- gets csDur
    put st {csDur = max d1 d2}
    unless (t1 == t2) (throwTy "match branches disagree (simplified)")
    pure (t1, c0 <> cn1 <> cn2 <> cnG)
  ELet x ty e1 e2 -> do
    (et1, cn1) <- typeCheckExpr ct e1
    st <- get
    d1 <- gets csDur
    delta <- gets csDelta
    case et1 of
      RTFut{} -> do
        let dlt' = Map.insert x et1 (csDelta st)
        put st {csDelta = dlt'}
        (et2, cn2) <- typeCheckExpr ct e2
        pure (et2, cn1 <> cn2)
      DTBase{} -> do
        unless (cmpTy ty et1) (throwTy "let binding type mismatch")
        let cnC = cnstrC (annotationOf et1) delta d1
            gam' = Map.insert x et1 (csGamma st)
        put st {csGamma = gam'}
        (et2, cn2) <- typeCheckExpr ct e2
        pure (et2, cn1 <> cn2 <> cnC)
      DTRes{} -> do
        unless (cmpTy ty et1) (throwTy "let binding type mismatch")
        let cnC = cnstrC (annotationOf et1) delta d1
            gam' = Map.insert x et1 (csGamma st)
        put st {csGamma = gam'}
        (et2, cn2) <- typeCheckExpr ct e2
        pure (et2, cn1 <> cn2 <> cnC)
      _ -> throwTy "let expects data or future type"
  EAddCon ve pol -> do
    (etu, c0) <- typeCheckValExpr ct ve
    uvar <- case ve of VVar xv -> pure xv; _ -> throwTy "addCon expects user variable"
    case etu of
      RTUser _ -> pure ()
      _ -> throwTy "addCon expects user type"
    st <- get
    -- Paper (t-add-cons): record R + <C,a,delta'+delta> where delta is the current offset.
    d <- gets csDur
    let polDur = polDuration pol + d
        upd = \case
          RTUser r -> RTUser (PAdd r (polClass pol) (polAction pol) (polPurpose pol) polDur)
          _ -> RTUser (PAdd PBase (polClass pol) (polAction pol) (polPurpose pol) polDur)
        dlt0 = csDelta st
        dlt' = Map.alter (Just . maybe (upd (RTUser PBase)) upd) uvar dlt0
    put st {csDelta = dlt'}
    pure (DTBase TUnit TAEmpty, c0)

typeCheckMethod :: ClassTable -> ClassName -> MethodDecl -> Either TypeError (CnstrSet, Set VarName)
typeCheckMethod ct cname md = runExcept $ evalStateT go initSt
 where
  cls = lookupClass ct cname
  allP = ctPurposes ct
  (g0, d0) = buildInitialEnvs allP (mdParams md) (cdFields cls)
  initSt =
    CheckerState
      { csGamma = g0
      , csDelta = d0
      , csDur = 0
      , csFresh = 0
      , csPurposes = allP
      , csClass = cname
      }
  go = do
    (retTy, cn) <- typeCheckExpr ct (mdBody md)
    dOut <- gets csDur
    delta <- gets csDelta
    let retAnn = annotationOf retTy
        cnRet = cnstrT retAnn delta dOut
    delta' <- gets csDelta
    let um =
          Set.fromList
            [ xv
            | (xv, RTUser r) <- Map.toList delta'
            , r /= PBase
            ]
    pure (cn <> cnRet, um)

typeCheckClass :: ClassTable -> ClassDecl -> Either TypeError [(MethodName, CnstrSet, Set VarName)]
typeCheckClass ct cls = do
  -- Paper (t-class): fields must not have user type.
  unless (all (\(ty, _) -> ty /= TUser) (cdFields cls)) $
    Left (TypeError ("class " ++ cdName cls ++ ": fields must not have user type"))
  forM (cdMethods cls) $ \m -> do
    (cn, um) <- typeCheckMethod ct (cdName cls) m
    pure (mdName m, cn, um)

inferMethodMeta :: ClassTable -> Either TypeError ClassTable
inferMethodMeta ct0 = do
  pairs <-
    fmap concat $
      forM (Map.elems (ctClasses ct0)) $ \cls -> do
        rows <- typeCheckClass ct0 cls
        pure [((cdName cls, nm), (cn, um)) | (nm, cn, um) <- rows]
  pure ct0 {ctMethodMeta = Map.fromList pairs}

-- Computed output offset for a method body
methodDeltaOut :: ClassTable -> ClassName -> MethodDecl -> Either TypeError Duration
methodDeltaOut ct cname md = runExcept $ evalStateT go initSt
 where
  cls = lookupClass ct cname
  allP = ctPurposes ct
  (g0, d0) = buildInitialEnvs allP (mdParams md) (cdFields cls)
  initSt =
    CheckerState
      { csGamma = g0
      , csDelta = d0
      , csDur = 0
      , csFresh = 0
      , csPurposes = allP
      , csClass = cname
      }
  go = do
    _ <- typeCheckExpr ct (mdBody md)
    gets csDur
