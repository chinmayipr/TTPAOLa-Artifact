{-# LANGUAGE LambdaCase #-}
module TyPAOL.Eval where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import TyPAOL.Consent (RTag (..), tagCombine, tagFromSource)
import TyPAOL.Runtime
import TyPAOL.Syntax

data EvalError
  = UndefinedField FieldName
  | BadOperands BinOp Value Value
  | FreeVariable VarName
  deriving (Eq, Show)


evalVE :: Map FieldName TaggedVal -> ValExpr -> Either EvalError TaggedVal
evalVE phi = \case
  VLitInt n -> Right (TaggedVal (VInt_ n) RTagEmpty)
  VLitBool b -> Right (TaggedVal (VBool_ b) RTagEmpty)
  VLitUnit -> Right (TaggedVal VUnit_ RTagEmpty)
  VLitUser u -> Right (TaggedVal (VUserId_ u) RTagEmpty)
  VLitObj o -> Right (TaggedVal (VObjId_ o) RTagEmpty)
  VLitFut f -> Right (TaggedVal (VFutId_ f) RTagEmpty)
  VField f -> case Map.lookup f phi of
    Just tv -> Right tv
    Nothing -> Left (UndefinedField f)
  VVar x -> Left (FreeVariable x)
  VThis -> Left (FreeVariable "this")
  VOp op e1 e2 -> do
    TaggedVal v1 t1 <- evalVE phi e1
    TaggedVal v2 t2 <- evalVE phi e2
    v <- applyOp op v1 v2
    Right (TaggedVal v (tagCombine t1 t2))
  VTag ve t -> do
    TaggedVal v tv <- evalVE phi ve
    Right (TaggedVal v (tagCombine tv (tagFromSource t)))
  VOk ve -> do
    tv <- evalVE phi ve
    Right (TaggedVal (VOk_ tv) (tvTag tv))
  VErr ve -> do
    tv <- evalVE phi ve
    Right (TaggedVal (VErr_ tv) (tvTag tv))

applyOp :: BinOp -> Value -> Value -> Either EvalError Value
applyOp Add (VInt_ a) (VInt_ b) = Right (VInt_ (a + b))
applyOp Sub (VInt_ a) (VInt_ b) = Right (VInt_ (a - b))
applyOp Mul (VInt_ a) (VInt_ b) = Right (VInt_ (a * b))
applyOp Div (VInt_ a) (VInt_ b)
  | b == 0 = Left (BadOperands Div (VInt_ a) (VInt_ b))
  | otherwise = Right (VInt_ (a `div` b))
applyOp And (VBool_ a) (VBool_ b) = Right (VBool_ (a && b))
applyOp Or (VBool_ a) (VBool_ b) = Right (VBool_ (a || b))
applyOp Eq (VInt_ a) (VInt_ b) = Right (VBool_ (a == b))
applyOp Lt (VInt_ a) (VInt_ b) = Right (VBool_ (a < b))
applyOp Gt (VInt_ a) (VInt_ b) = Right (VBool_ (a > b))
applyOp op v1 v2 = Left (BadOperands op v1 v2)
