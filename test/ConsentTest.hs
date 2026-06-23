module ConsentTest where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Hspec

import TyPAOL.Consent
import TyPAOL.Syntax (Action (..), ClassName)

spec :: Spec
spec = describe "TyPAOL.Consent" $ do
  it "tagCombine identity (left)" $ do
    let x = RTag (Set.fromList ["u"]) (Set.fromList ["p"])
    tagCombine RTagEmpty x `shouldBe` x

  it "tagCombine intersects purposes and unions users" $ do
    let t1 = RTag (Set.fromList ["a"]) (Set.fromList ["p1", "p2"])
        t2 = RTag (Set.fromList ["b"]) (Set.fromList ["p2", "p3"])
    tagCombine t1 t2 `shouldBe` RTag (Set.fromList ["a", "b"]) (Set.fromList ["p2"])

  it "tagCombine GLB property (finite sample)" $ do
    let t1 = RTag (Set.fromList ["a"]) (Set.fromList ["p1", "p2"])
        t2 = RTag (Set.fromList ["b"]) (Set.fromList ["p2", "p3"])
        g = tagCombine t1 t2
    tagLeq g t1 `shouldBe` True

  it "allowedActions anti-monotone in tau" $ do
    let cname :: ClassName
        cname = "Courier"
        u = "u1"
        p = "p0"
        pm =
          Map.singleton
            Use
            (Set.singleton (CE cname p 15))
        sigma = Map.singleton u pm
        t = RTag (Set.singleton u) (Set.singleton p)
        a10 = allowedActions sigma cname t 10
        a20 = allowedActions sigma cname t 20
    a20 `Set.isSubsetOf` a10 `shouldBe` True

  it "complyU false on expired consent" $ do
    let cname = "Courier"
        u = "u1"
        p = "p0"
        pm = Map.singleton Use (Set.singleton (CE cname p 10))
        sigma = Map.singleton u pm
        t = RTag (Set.singleton u) (Set.singleton p)
    complyU sigma cname t 12 `shouldBe` False

  it "remExpired keeps entries expiring at tau" $ do
    let u = "u1"
        cname = "Courier"
        p = "p0"
        pm = Map.singleton Collect (Set.fromList [CE cname p 12, CE cname p 9])
        sigma = Map.singleton u pm
        sigma' = remExpired sigma 12
        entries = maybe Set.empty id (Map.lookup u sigma' >>= Map.lookup Collect)
    Set.map ceExpiry entries `shouldBe` Set.singleton 12

  it "addConsent: same (class,purpose) for an action is overwritten" $ do
    -- This exercises the new ClassName-based key (was EntityName before).
    let u = "u1"
        c = "Courier"
        p = "Delivery"
        s0 = addConsent Map.empty u c Use p 50
        s1 = addConsent s0       u c Use p 20
        entries =
          maybe Set.empty id (Map.lookup u s1 >>= Map.lookup Use)
    Set.map ceExpiry entries `shouldBe` Set.singleton 20
