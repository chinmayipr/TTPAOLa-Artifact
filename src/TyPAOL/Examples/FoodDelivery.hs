module TyPAOL.Examples.FoodDelivery where

import qualified Data.Set as Set

import TyPAOL.Syntax

-- Purposes are preserved (the running example uses only Delivery).
foodDelivery :: Program
foodDelivery =
  Program
    { prgPurposes = ["Delivery"]
    , prgClasses = [plat, courier]
    , prgMain = bootstrap
    }

tD :: Type
tD = TPersonal TInt 

tagDelivery :: VarName -> Tag
tagDelivery u = TagExpr (Set.singleton u) (Set.singleton "Delivery")

seqLet :: Expr -> Expr -> Expr
seqLet = seqE

plat :: ClassDecl
plat =
  ClassDecl
    { cdName = "Plat"
    , cdParams = []
    , cdFields = [(tD, "addrDB")] 
    , cdMethods = [setAddrCons, renewCons, getAddr]
    }
 where
  setAddrCons =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "setAddrCons"
      , mdParams = [(TUser, "u1"), (tD, "rawAddr")]
      , mdBody =
          seqLet (EAddCon (VVar "u1") (Policy "Courier" Use      "Delivery" 50)) $
            seqLet (EAddCon (VVar "u1") (Policy "Courier" Collect  "Delivery" 50)) $
              seqLet (EAddCon (VVar "u1") (Policy "Courier" Transfer "Delivery" 50)) $
                EVal VLitUnit
      }

  renewCons =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "renewCons"
      , mdParams = [(TUser, "u4")]
      , mdBody =
          seqLet (EAddCon (VVar "u4") (Policy "Courier" Use      "Delivery" 20)) $
            seqLet (EAddCon (VVar "u4") (Policy "Courier" Transfer "Delivery" 20)) $
              EVal VLitUnit
      }

  getAddr =
    MethodDecl
      { mdRetType = tD
      , mdRetAnn = TA Set.empty (tagDelivery "u2")
      , mdName = "getAddr"
      , mdParams = [(TUser, "u2")]
      , mdBody =
          seqLet (EDelay 1) $
            ELet "x" tD (EVal (VField "addrDB")) $
              ELet "y" tD
                (EVal (VTag (VVar "x") (tagDelivery "u2")))
                (EVal (VVar "y"))
      }

-- Courier class: holds a reference to the platform.
courier :: ClassDecl
courier =
  ClassDecl
    { cdName = "Courier"
    , cdParams = [(TClass "Plat", "p")]
    , cdFields = [(TClass "Plat", "p")]
    , cdMethods = [deliver]
    }
 where
  deliver =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "deliver"
      , mdParams = [(TUser, "u3"), (tD, "order")]
      , mdBody =
      
          ELet "f" tD
            (EAsyncCall (VField "p") "getAddr" [VVar "u3"]) $
            ELet "res" tD
              (EFetch (VVar "f") 4 (VLitInt 0))
              ( EMatch
                  (VVar "res")
                  "addr"
                  ( EIf
                      (VLitBool True) 
                      ( seqLet (EDelay 5)  $
                          ELet "_z" tD (EVal (VVar "addr")) (EVal VLitUnit)
                      )
                      ( seqLet (EDelay 10) $
                          ELet "_z" tD (EVal (VVar "addr")) (EVal VLitUnit)
                      )
                  )
                  "_"
                  (EVal VLitUnit)
              )
      }

bootstrap :: [MainStmt]
bootstrap =
  [ MNewObj "Plat" "plat" []
  , MNewObj "Courier" "cr" ["plat"]
  , MNewUser "alice"
  , MAddCon "alice" (Policy "Plat" Use      "Delivery" 80)
  , MAddCon "alice" (Policy "Plat" Collect  "Delivery" 80)
  , MAddCon "alice" (Policy "Plat" Store    "Delivery" 80)
  , MAddCon "alice" (Policy "Plat" Transfer "Delivery" 80)
  ]
