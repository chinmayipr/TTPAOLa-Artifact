module TyPAOL.Runtime where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Set (Set)
import qualified Data.Set as Set
import TyPAOL.Syntax
import TyPAOL.Consent (ConsentEnv, RTag (..), addConsent)
import TyPAOL.Types (CnstrSet, DeltaEnv)

data TaggedVal = TaggedVal {tvValue :: Value, tvTag :: RTag}
  deriving (Eq, Show)

data Value
  = VInt_ Int
  | VBool_ Bool
  | VUnit_
  | VUserId_ UserId
  | VObjId_ ObjId
  | VFutId_ FutId
  | VOk_ TaggedVal
  | VErr_ TaggedVal
  deriving (Eq, Show)

data TypedThreadMeta = TypedThreadMeta
  { ttmUm :: Set UserId
  , ttmUc :: Set UserId
  }
  deriving (Eq, Show)

data Config = Config
  { cfgObjects :: Map ObjId Object
  , cfgMessages :: [Message]
  , cfgFutures :: Map FutId (Maybe TaggedVal) 
  , cfgConsent :: ConsentEnv
  , cfgTime :: Int
  , cfgFreshCtr :: Int
  , cfgVarStore :: Map VarName TaggedVal 
  , cfgDefaultClass :: ClassName 
  }
  deriving (Show)

data Object = Object
  { objFields :: Map FieldName TaggedVal 
  , objThread :: Thread 
  , objQueue :: [QueueSlot] 
  , objClass :: ClassName 
  }
  deriving (Show)

data Thread
  = Idle
  | Running RunThread
  deriving (Show)

data RunThread = RunThread
  { rtExpr :: Expr
  , rtFut :: FutId
  , rtAccClass :: ClassName 
  , rtTypedMeta :: Maybe TypedThreadMeta
  }
  deriving (Show)

data QueueEntry = QueueEntry
  { qeExpr :: Expr
  , qeFut :: FutId
  , qeAccClass :: ClassName 
  }
  deriving (Show)

data TypedQueueEntry = TQE
  { tqeExpr :: Expr
  , tqeFut :: FutId
  , tqeAccClass :: ClassName 
  , tqeParams :: Map VarName TaggedVal
  , tqeCn :: CnstrSet
  , tqeUmVars :: Set VarName
  , tqeDelta :: DeltaEnv
  }
  deriving (Show)

data QueueSlot = QUntyped QueueEntry | QTyped TypedQueueEntry
  deriving (Show)

data Message = Message
  { msgMethod :: MethodName
  , msgCallee :: ObjId
  , msgArgs :: [TaggedVal]
  , msgFut :: FutId
  , msgCallerClass :: ClassName 
  }
  deriving (Eq, Show)

data ClassTable = ClassTable
  { ctFields :: Map ClassName [FieldName]
  , ctMBody :: Map (ClassName, MethodName) ([VarName], Expr)
  , ctMType :: Map (ClassName, MethodName) ([Type], Type, TagAnnotation)
  , ctClasses :: Map ClassName ClassDecl
  , ctPurposes :: Set Purpose
  , ctMethodMeta :: Map (ClassName, MethodName) (CnstrSet, Set VarName)
  }
  deriving (Show)

buildClassTable :: Program -> ClassTable
buildClassTable prg =
  ClassTable
    { ctFields = Map.fromList [(cdName c, map snd (cdFields c)) | c <- prgClasses prg]
    , ctMBody =
        Map.fromList
          [ ((cdName c, mdName m), (map snd (mdParams m), mdBody m))
          | c <- prgClasses prg
          , m <- cdMethods c
          ]
    , ctMType =
        Map.fromList
          [ ( (cdName c, mdName m)
            , (map fst (mdParams m), mdRetType m, mdRetAnn m)
            )
          | c <- prgClasses prg
          , m <- cdMethods c
          ]
    , ctClasses = Map.fromList [(cdName c, c) | c <- prgClasses prg]
    , ctPurposes = Set.fromList (prgPurposes prg)
    , ctMethodMeta = Map.empty
    }

initConfig :: Program -> ClassTable -> Config
initConfig prg ct =
  foldl' execMainStmt cfg0 (prgMain prg)
 where
  defCls = case prgClasses prg of
    (c : _) -> cdName c
    [] -> "Main"
  cfg0 =
    Config
      { cfgObjects = Map.empty
      , cfgMessages = []
      , cfgFutures = Map.empty
      , cfgConsent = Map.empty
      , cfgTime = 0
      , cfgFreshCtr = 0
      , cfgVarStore = Map.empty
      , cfgDefaultClass = defCls
      }

  execMainStmt :: Config -> MainStmt -> Config
  execMainStmt cfg stmt = case stmt of
    MNewUser x ->
      let (u, cfg1) = freshUser cfg
       in cfg1 {cfgVarStore = Map.insert x (TaggedVal (VUserId_ u) RTagEmpty) (cfgVarStore cfg1)}
    MNewObj cname x args ->
      let cls = requireClass cname
          (oid, cfg1) = freshObjId cfg
          paramTVs =
            Map.fromList
              [ (pname, lookupVar v cfg1)
              | ((_, pname), v) <- zip (cdParams cls) args
              ]
          fields1 =
            Map.fromList
              [ ( fn
                , Map.findWithDefault (TaggedVal VUnit_ RTagEmpty) fn paramTVs
                )
              | (_, fn) <- cdFields cls
              ]
          obj =
            Object
              { objFields = fields1
              , objThread = Idle
              , objQueue = []
              , objClass = cname
              }
       in cfg1
            { cfgObjects = Map.insert oid obj (cfgObjects cfg1)
            , cfgVarStore = Map.insert x (TaggedVal (VObjId_ oid) RTagEmpty) (cfgVarStore cfg1)
            }
    MAddCon x pol ->
      let TaggedVal (VUserId_ u) _ = lookupVar x cfg
          absExp = cfgTime cfg + polDuration pol
          sigma' = addConsent (cfgConsent cfg) u (polClass pol) (polAction pol) (polPurpose pol) absExp
       in cfg {cfgConsent = sigma'}
    MAsyncCall x m argVars ->
      let TaggedVal (VObjId_ oid) _ = lookupVar x cfg
          args = [lookupVar v cfg | v <- argVars]
          (fut, cfg1) = freshFut cfg
          msg =
            Message
              { msgMethod = m
              , msgCallee = oid
              , msgArgs = args
              , msgFut = fut
              , msgCallerClass = cfgDefaultClass cfg
              }
       in cfg1
            { cfgMessages = cfgMessages cfg1 ++ [msg]
            , cfgFutures = Map.insert fut Nothing (cfgFutures cfg1)
            }

  requireClass :: ClassName -> ClassDecl
  requireClass nm =
    maybe (error ("Unknown class: " ++ nm)) id (Map.lookup nm (ctClasses ct))

  lookupVar :: VarName -> Config -> TaggedVal
  lookupVar v cfg = maybe (error ("Unknown variable: " ++ v)) id (Map.lookup v (cfgVarStore cfg))

freshUser :: Config -> (UserId, Config)
freshUser cfg =
  let n = cfgFreshCtr cfg
      u = "user_" ++ show n
   in (u, cfg {cfgFreshCtr = n + 1})

freshObjId :: Config -> (ObjId, Config)
freshObjId cfg =
  let n = cfgFreshCtr cfg
      o = "obj_" ++ show n
   in (o, cfg {cfgFreshCtr = n + 1})

freshFut :: Config -> (FutId, Config)
freshFut cfg =
  let n = cfgFreshCtr cfg
      f = "fut_" ++ show n
   in (f, cfg {cfgFreshCtr = n + 1})
