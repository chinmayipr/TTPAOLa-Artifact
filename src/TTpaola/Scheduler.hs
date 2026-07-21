{-# LANGUAGE LambdaCase #-}
module TTpaola.Scheduler where

import Control.Monad.Except
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import TTpaola.Interpreter
import TTpaola.Runtime
import TTpaola.Syntax (Duration, MethodName, ObjId)
import TTpaola.TypedInterpreter (activateTyped, bindMessageTyped, stepInstantTyped)

data StepResult
  = StepInstant ObjId
  | StepBind MethodName ObjId
  | StepActivate ObjId
  | StepTimeAdv Duration Int
  | StepStuck
  deriving (Show)

tryInstantAll :: ClassTable -> Bool -> InterpM (Maybe StepResult)
tryInstantAll ct typed = do
  objs <- gets cfgObjects
  go (Map.keys objs)
 where
  go [] = pure Nothing
  go (oid : xs) = do
    obj <- getObject oid
    case objThread obj of
      Idle -> go xs
      Running _ ->
        catchError
          ( do
              e' <-
                if typed
                  then stepInstantTyped ct oid obj
                  else stepInstant ct oid obj
              objNow <- getObject oid
              case objThread objNow of
                Running rtNow ->
                  putObject oid (objNow {objThread = Running (rtNow {rtExpr = e'})})
                Idle -> pure ()
              pure (Just (StepInstant oid))
          )
          ( \case
              NoRuleApplies -> go xs
              e -> throwError e
          )

tryBind :: ClassTable -> Bool -> InterpM (Maybe StepResult)
tryBind ct typed = do
  msgs <- gets cfgMessages
  case msgs of
    [] -> pure Nothing
    (m : _) -> do
      if typed then bindMessageTyped ct m else bindMessage ct m
      pure (Just (StepBind (msgMethod m) (msgCallee m)))

tryActivate :: Bool -> InterpM (Maybe StepResult)
tryActivate typed = do
  objs <- gets cfgObjects
  go (Map.keys objs)
 where
  go [] = pure Nothing
  go (oid : xs) = do
    ok <- if typed then activateTyped oid else activateUntyped oid
    if ok then pure (Just (StepActivate oid)) else go xs

tryTime :: InterpM (Maybe StepResult)
tryTime = do
  catchError
    ( do
        t0 <- gets cfgTime
        timeAdv
        t1 <- gets cfgTime
        pure (Just (StepTimeAdv (max 0 (t1 - t0)) t1))
    )
    ( \case
        NoProgress -> pure Nothing
        e -> throwError e
    )

step :: ClassTable -> Bool -> InterpM StepResult
step ct typed = do
  r1 <- tryInstantAll ct typed
  case r1 of
    Just x -> pure x
    Nothing -> do
      r2 <- tryBind ct typed
      case r2 of
        Just x -> pure x
        Nothing -> do
          r3 <- tryActivate typed
          case r3 of
            Just x -> pure x
            Nothing -> do
              r4 <- tryTime
              case r4 of
                Just x -> pure x
                Nothing -> pure StepStuck

run :: ClassTable -> Bool -> InterpM [StepResult]
run ct typed = do
  r <- step ct typed
  case r of
    StepStuck -> pure [StepStuck]
    _ -> (r :) <$> run ct typed
