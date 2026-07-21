module TTpaola.Types where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import Data.Set (Set)
import TTpaola.Syntax
  ( Action
  , ClassName
  , Duration
  , FieldName
  , Purpose
  , Tag (..)
  , TagAnnotation (..)
  , Type (..)
  , VarName
  , VarRef (..)
  )

import TTpaola.Consent (tagCombineSrc, tagLeqSrc)

data AConstraint = ACnstr
  { acAction :: Action
  , acAnn :: TagAnnotation
  , acDelta :: DeltaEnv
  , acDur :: Duration
  }
  deriving (Eq, Ord, Show)

type CnstrSet = Set AConstraint

data ExtType
  = DTBase Type TagAnnotation 
  | DTRes Type TagAnnotation 
  | RTUser PolicyExpr 
  | RTClass ClassName (Maybe ClassName) 
  | RTFut Type TagAnnotation 
  deriving (Eq, Ord, Show)

data PolicyExpr
  = PBase
  | PAdd PolicyExpr ClassName Action Purpose Duration
  deriving (Eq, Ord, Show)

type GammaEnv = Map VarName ExtType

type DeltaEnv = Map VarName ExtType

taCompose :: TagAnnotation -> TagAnnotation -> TagAnnotation
taCompose TAEmpty ta = ta
taCompose ta TAEmpty = ta
taCompose (TA vr1 t1) (TA vr2 t2) = TA (Set.union vr1 vr2) (tagCombineSrc t1 t2)

taLeq :: TagAnnotation -> TagAnnotation -> Bool
taLeq _ TAEmpty = True
taLeq TAEmpty (TA _ _) = False
taLeq (TA vr1 t1) (TA vr2 t2) = Set.isSubsetOf vr2 vr1 && tagLeqSrc t1 t2

taSubst :: TagAnnotation -> VarRef -> TagAnnotation -> TagAnnotation
taSubst TAEmpty _ _ = TAEmpty
taSubst (TA vrs t) vr ann'
  | vr `Set.member` vrs = taCompose (TA (Set.delete vr vrs) t) ann'
  | otherwise = TA vrs t

annotationOf :: ExtType -> TagAnnotation
annotationOf (DTBase _ ann) = ann
annotationOf (DTRes _ ann) = ann
annotationOf (RTFut _ ann) = ann
annotationOf _ = TAEmpty

cmpTy :: Type -> ExtType -> Bool
cmpTy (TClass c1) (RTClass c2 _) = c1 == c2
cmpTy TUser (RTUser _) = True
-- Primitive / personal data: allow any tag annotation; personal B# is
-- compatible with B when the underlying base matches (ops on personal Int, etc.).
cmpTy TInt (DTBase TInt _) = True
cmpTy TInt (DTBase (TPersonal TInt) _) = True
cmpTy TBool (DTBase TBool _) = True
cmpTy TBool (DTBase (TPersonal TBool) _) = True
cmpTy TUnit (DTBase TUnit _) = True
cmpTy t (DTBase t' TAEmpty) = t == t' || matchPersonal t t'
cmpTy (TPersonal t) (DTBase (TPersonal t') _) = t == t'
cmpTy (TPersonal t) (DTBase t' _) = t == t'
cmpTy TInt (DTRes TInt _) = True
cmpTy TInt (DTRes (TPersonal TInt) _) = True
cmpTy TBool (DTRes TBool _) = True
cmpTy TBool (DTRes (TPersonal TBool) _) = True
cmpTy t (DTRes t' TAEmpty) = t == t' || matchPersonal t t'
cmpTy (TPersonal t) (DTRes (TPersonal t') _) = t == t'
cmpTy (TPersonal t) (DTRes t' _) = t == t'
cmpTy _ _ = False

-- matchPersonal (TPersonal t) t' holds iff t == t'.
matchPersonal :: Type -> Type -> Bool
matchPersonal (TPersonal t) t' = t == t'
matchPersonal _ _ = False

-- initial environments from parameter/field declarations
buildInitialEnvs :: Set Purpose -> [(Type, VarName)] -> [(Type, FieldName)] -> (GammaEnv, DeltaEnv)
buildInitialEnvs allPurposes params fields =
  ( Map.unions (map gammaOf params)
      `Map.union` Map.unions (map gammaField fields)
  , Map.unions (map deltaOf params)
      `Map.union` Map.unions (map deltaField fields)
  )
 where
  gammaOf :: (Type, VarName) -> GammaEnv
  gammaOf (ty, vr) = case ty of
    TPersonal bt ->
      Map.singleton vr $
        DTBase (TPersonal bt) (TA (Set.singleton (RefVar vr)) (TagExpr Set.empty allPurposes))
    TInt -> Map.singleton vr (DTBase TInt TAEmpty)
    TBool -> Map.singleton vr (DTBase TBool TAEmpty)
    TUnit -> Map.singleton vr (DTBase TUnit TAEmpty)
    TClass {} -> Map.empty
    TUser -> Map.empty

  gammaField :: (Type, FieldName) -> GammaEnv
  gammaField (ty, fn) = case ty of
    TPersonal bt ->
      Map.singleton fn $
        DTBase (TPersonal bt) (TA (Set.singleton (RefField fn)) (TagExpr Set.empty allPurposes))
    TInt -> Map.singleton fn (DTBase TInt TAEmpty)
    TBool -> Map.singleton fn (DTBase TBool TAEmpty)
    TUnit -> Map.singleton fn (DTBase TUnit TAEmpty)
    TClass {} -> Map.empty
    TUser -> Map.empty

  deltaOf :: (Type, VarName) -> DeltaEnv
  deltaOf (ty, vr) = case ty of
    TClass c -> Map.singleton vr (RTClass c Nothing)
    TUser -> Map.singleton vr (RTUser PBase)
    _ -> Map.empty

  deltaField :: (Type, FieldName) -> DeltaEnv
  deltaField (ty, fn) = case ty of
    TClass c -> Map.singleton fn (RTClass c Nothing)
    TUser -> Map.singleton fn (RTUser PBase)
    _ -> Map.empty
