{-# LANGUAGE LambdaCase #-}
module TyPAOL.Syntax where

import Data.Set (Set)
import qualified Data.Set as Set

-- Identifiers are all plain strings.
type VarName = String
type FieldName = String
type MethodName = String
type ClassName = String
type Purpose = String
type UserId = String
type ObjId = String
type FutId = String
type Duration = Int -- discrete time units, always >= 0

-- GDPR actions.
data Action = Use | Collect | Store | Transfer
  deriving (Eq, Ord, Show, Enum, Bounded)

data Tag = TagEmpty | TagExpr (Set VarName) (Set Purpose)
  deriving (Eq, Ord, Show)

data Policy = Policy
  { polClass :: ClassName
  , polAction :: Action
  , polPurpose :: Purpose
  , polDuration :: Duration
  }
  deriving (Eq, Show)

data BinOp = Add | Sub | Mul | Div | And | Or | Eq | Lt | Gt
  deriving (Eq, Show)

data Type
  = TInt | TBool | TUnit
  | TPersonal Type -- personal data
  | TClass ClassName
  | TUser
  deriving (Eq, Ord, Show)

data ValExpr
  = VVar VarName 
  | VField FieldName 
  | VThis 
  | VLitInt Int
  | VLitBool Bool
  | VLitUnit 
  | VLitUser UserId 
  | VLitObj ObjId 
  | VLitFut FutId 
  | VOp BinOp ValExpr ValExpr 
  | VTag ValExpr Tag 
  | VOk ValExpr 
  | VErr ValExpr 
  deriving (Eq, Show)

data Expr
  = EVal ValExpr 
  | EAssign FieldName ValExpr 
  | EAsyncCall ValExpr MethodName [ValExpr] 
  | EAddCon ValExpr Policy 
  | EFetch ValExpr Duration ValExpr 
  | EIf ValExpr Expr Expr 
  | ELet VarName Type Expr Expr 
  | EDelay Duration 
  | EMatch ValExpr VarName Expr VarName Expr 
  deriving (Eq, Show)

-- Sequencing is sugar for a let with a wildcard binder.
seqE :: Expr -> Expr -> Expr
seqE e1 e2 = ELet "_" TUnit e1 e2

data TagAnnotation = TAEmpty | TA (Set VarRef) Tag
  deriving (Eq, Ord, Show)

data VarRef = RefVar VarName | RefField FieldName
  deriving (Eq, Ord, Show)

data MethodDecl = MethodDecl
  { mdRetType :: Type
  , mdRetAnn :: TagAnnotation 
  , mdName :: MethodName
  , mdParams :: [(Type, VarName)]
  , mdBody :: Expr
  }
  deriving (Eq, Show)

data ClassDecl = ClassDecl
  { cdName :: ClassName
  , cdParams :: [(Type, VarName)] 
  , cdFields :: [(Type, FieldName)]
  , cdMethods :: [MethodDecl]
  }
  deriving (Eq, Show)

-- Program (class names serve as entities)
data Program = Program
  { prgPurposes :: [Purpose]
  , prgClasses :: [ClassDecl]
  , prgMain :: [MainStmt]
  }
  deriving (Eq, Show)

data MainStmt
  = MNewObj ClassName VarName [VarName]
  | MNewUser VarName
  | MAddCon VarName Policy
  | MAsyncCall VarName MethodName [VarName]
  deriving (Eq, Show)

-- Free variables in a value expression (excluding this).
freeVarsVal :: ValExpr -> Set VarName
freeVarsVal = \case
  VVar v -> Set.singleton v
  VField _ -> Set.empty
  VThis -> Set.empty
  VLitInt _ -> Set.empty
  VLitBool _ -> Set.empty
  VLitUnit -> Set.empty
  VLitUser _ -> Set.empty
  VLitObj _ -> Set.empty
  VLitFut _ -> Set.empty
  VOp _ a b -> freeVarsVal a `Set.union` freeVarsVal b
  VTag ve (TagExpr vs _) -> freeVarsVal ve `Set.union` vs
  VTag ve TagEmpty -> freeVarsVal ve
  VOk ve -> freeVarsVal ve
  VErr ve -> freeVarsVal ve

freeVarsExpr :: Expr -> Set VarName
freeVarsExpr = \case
  EVal ve -> freeVarsVal ve
  EAssign _ ve -> freeVarsVal ve
  EAsyncCall ve _ args -> freeVarsVal ve `Set.union` Set.unions (map freeVarsVal args)
  EAddCon ve _ -> freeVarsVal ve
  EFetch ve _ ve' -> freeVarsVal ve `Set.union` freeVarsVal ve'
  EIf ve e1 e2 -> freeVarsVal ve `Set.union` freeVarsExpr e1 `Set.union` freeVarsExpr e2
  ELet x _ e1 e2 ->
    freeVarsExpr e1 `Set.union` (freeVarsExpr e2 Set.\\ Set.singleton x)
  EDelay _ -> Set.empty
  EMatch ve xv e1 yv e2 ->
    freeVarsVal ve
      `Set.union` (freeVarsExpr e1 Set.\\ Set.singleton xv)
      `Set.union` (freeVarsExpr e2 Set.\\ Set.singleton yv)

substTag :: VarName -> ValExpr -> Tag -> Tag
substTag x rep = \case
  TagEmpty -> TagEmpty
  TagExpr vs ps ->
    TagExpr (Set.delete x vs `Set.union` extraUsers) ps
   where
    extraUsers =
      if x `Set.member` vs
        then case rep of
          VVar y -> Set.singleton y
          VLitUser u -> Set.singleton u
          _ -> Set.empty
        else Set.empty

substitute :: VarName -> ValExpr -> Expr -> Expr
substitute x rep = goE
 where
  repFvs = freeVarsVal rep

  goE :: Expr -> Expr
  goE e0 = case e0 of
    EVal ve -> EVal (goV ve)
    EAssign f ve -> EAssign f (goV ve)
    EAsyncCall ve m args -> EAsyncCall (goV ve) m (map goV args)
    EAddCon ve pol -> EAddCon (goV ve) pol
    EFetch ve d ve' -> EFetch (goV ve) d (goV ve')
    EIf ve e1 e2 -> EIf (goV ve) (goE e1) (goE e2)
    ELet y ty e1 e2
      | y == x ->
          ELet y ty (goE e1) e2
      | not (Set.null (Set.singleton y `Set.intersection` repFvs)) ->
          let y' = freshVar y (Set.unions [freeVarsExpr e1, freeVarsExpr e2, repFvs, Set.singleton x])
              e1' = renameExpr y y' e1
              e2' = renameExpr y y' e2
           in ELet y' ty (goE e1') (goE e2')
      | otherwise ->
          ELet y ty (goE e1) (goE e2)
    EDelay d -> EDelay d
    EMatch ve xv e1 yv e2 ->
      let ve' = goV ve
          (xv', e1') = bindCase xv e1
          (yv', e2') = bindCase yv e2
       in EMatch ve' xv' e1' yv' e2'
     where
      bindCase :: VarName -> Expr -> (VarName, Expr)
      bindCase bv body
        | bv == x = (bv, body)
        | not (Set.null (Set.singleton bv `Set.intersection` repFvs)) =
            let bv' = freshVar bv (Set.unions [freeVarsExpr body, repFvs, Set.singleton x, freeVarsVal ve])
             in (bv', renameExpr bv bv' body)
        | otherwise = (bv, goE body)

  goV :: ValExpr -> ValExpr
  goV = substituteVal x rep

substituteVal :: VarName -> ValExpr -> ValExpr -> ValExpr
substituteVal x rep = \case
  VVar y | y == x -> rep
  VVar y -> VVar y
  VField f -> VField f
  VThis -> VThis
  l@VLitInt {} -> l
  l@VLitBool {} -> l
  VLitUnit -> VLitUnit
  l@VLitUser {} -> l
  l@VLitObj {} -> l
  l@VLitFut {} -> l
  VOp op a b -> VOp op (substituteVal x rep a) (substituteVal x rep b)
  VTag ve t -> VTag (substituteVal x rep ve) (substTag x rep t)
  VOk ve -> VOk (substituteVal x rep ve)
  VErr ve -> VErr (substituteVal x rep ve)

freshVar :: VarName -> Set VarName -> VarName
freshVar base avoid = head [cand | i <- [(0 :: Int) ..], let cand = if i == 0 then base else base ++ "_" ++ show i, cand `Set.notMember` avoid]

renameExpr :: VarName -> VarName -> Expr -> Expr
renameExpr from to = substitute from (VVar to)
