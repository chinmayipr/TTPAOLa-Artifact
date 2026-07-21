module TTpaola.Examples.FoodDelivery where

import qualified Data.Set as Set

import TTpaola.Syntax

-- Running example from the paper (Fig. 2 / Example 1-2).
-- Purposes are kept but only one top-level purpose "Delivery" is used.
--
-- Consent durations follow Example 2 Scenario 1/3 defaults:
--   delta1 = 11 (setAddrCons), delta2 = 6 (renewCons).
-- addrDB stores non-personal data; getAddr tags it as personal on return.
foodDelivery :: Program
foodDelivery =
  Program
    { prgPurposes = ["Delivery"]
    , prgClasses = [plat, courier]
    , prgMain = bootstrap
    }
tAddr :: Type
tAddr = TInt

tD :: Type
tD = TPersonal TInt

tagDelivery :: VarName -> Tag
tagDelivery u = TagExpr (Set.singleton u) (Set.singleton "Delivery")

seqLet :: Expr -> Expr -> Expr
seqLet = seqE

-- delta1 from Scenario 1.
delta1 :: Duration
delta1 = 11

-- delta2 from Scenario 3.
delta2 :: Duration
delta2 = 6

plat :: ClassDecl
plat =
  ClassDecl
    { cdName = "Plat"
    , cdParams = []
    , cdFields = [(tAddr, "addrDB")]
    , cdMethods = [setAddrCons, renewCons, getAddr]
    }
 where
  -- setAddrCons(U u1, D rawAddr):
  --   grant Courier {use,collect,trans} for delta1; store address; unit
  setAddrCons =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "setAddrCons"
      , mdParams = [(TUser, "u1"), (tAddr, "rawAddr")]
      , mdBody =
          seqLet (EAddCon (VVar "u1") (Policy "Courier" Use      "Delivery" delta1)) $
            seqLet (EAddCon (VVar "u1") (Policy "Courier" Collect  "Delivery" delta1)) $
              seqLet (EAddCon (VVar "u1") (Policy "Courier" Transfer "Delivery" delta1)) $
                seqLet (EAssign "addrDB" (VVar "rawAddr")) $
                  EVal VLitUnit
      }

  -- renewCons(U u4): grant Courier {use,trans} for delta2 (collect not renewed).
  renewCons =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "renewCons"
      , mdParams = [(TUser, "u4")]
      , mdBody =
          seqLet (EAddCon (VVar "u4") (Policy "Courier" Use      "Delivery" delta2)) $
            seqLet (EAddCon (VVar "u4") (Policy "Courier" Transfer "Delivery" delta2)) $
              EVal VLitUnit
      }

  -- getAddr(U u2): delay 1; read addrDB; tag with {u2}; return tagged personal data.
  getAddr =
    MethodDecl
      { mdRetType = tD
      , mdRetAnn = TA Set.empty (tagDelivery "u2")
      , mdName = "getAddr"
      , mdParams = [(TUser, "u2")]
      , mdBody =
          seqLet (EDelay 1) $
            ELet "x" tAddr (EVal (VField "addrDB")) $
              ELet "y" tD
                (EVal (VTag (VVar "x") (tagDelivery "u2")))
                (EVal (VVar "y"))
      }

courier :: ClassDecl
courier =
  ClassDecl
    { cdName = "Courier"
    , cdParams = [(TClass "Plat", "p")]
    , cdFields = [(TClass "Plat", "p")]
    , cdMethods = [deliver]
    }
 where
  -- deliver(U u3, D order):
  -- fetch getAddr with timeout 4, on Ok, branch on cityCenter(addr) (addr < 100) with delay 5 / delay 10, on Err, unit.
  -- Paper informal Cn is Use+Collect at offset 4 (fetch), delta_out = 14.
  deliver =
    MethodDecl
      { mdRetType = TUnit
      , mdRetAnn = TAEmpty
      , mdName = "deliver"
      , mdParams = [(TUser, "u3"), (tD, "order")]
      , mdBody =
          ELet "f" TUnit 
            (EAsyncCall (VField "p") "getAddr" [VVar "u3"]) $
            ELet "res" tD
              (EFetch (VVar "f") 4 (VLitInt 0))
              ( EMatch
                  (VVar "res")
                  "addr"
                  ( EIf
                      -- cityCenter(addr): addr < 100
                      (VOp Lt (VVar "addr") (VLitInt 100))
                      (seqLet (EDelay 5) (EVal VLitUnit))
                      (seqLet (EDelay 10) (EVal VLitUnit))
                  )
                  "_def"
                  (EVal VLitUnit)
              )
      }

-- Example 2 initial Sigma0: Plat use/collect/trans @80 (no Store; addr is non-personal).
bootstrap :: [MainStmt]
bootstrap =
  [ MNewObj "Plat" "plat" []
  , MNewObj "Courier" "cr" ["plat"]
  , MNewUser "alice"
  , MAddCon "alice" (Policy "Plat" Use      "Delivery" 80)
  , MAddCon "alice" (Policy "Plat" Collect  "Delivery" 80)
  , MAddCon "alice" (Policy "Plat" Transfer "Delivery" 80)
  ]
