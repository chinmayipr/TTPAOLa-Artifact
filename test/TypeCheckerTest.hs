module TypeCheckerTest where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Test.Hspec

import TTpaola.Syntax (Action (..), Tag (..), TagAnnotation (..))
import TTpaola.TypeChecker (cnstrC, cnstrS, cnstrT, cnstrU)
import TTpaola.Types (AConstraint (..))

spec :: Spec
spec = describe "TTpaola.TypeChecker" $ do
  it "CnstrC includes Collect and Use" $ do
    let ann = TA Set.empty (TagExpr Set.empty (Set.singleton "p"))
        delta = Map.empty
        cs = cnstrC ann delta 3
    any (\(ACnstr a _ _ _) -> a == Collect) (Set.toList cs) `shouldBe` True
    any (\(ACnstr a _ _ _) -> a == Use) (Set.toList cs) `shouldBe` True

  it "CnstrS includes Store" $ do
    let ann = TA Set.empty (TagExpr Set.empty (Set.singleton "p"))
        delta = Map.empty
        cs = cnstrS ann delta 2
    any (\(ACnstr a _ _ _) -> a == Store) (Set.toList cs) `shouldBe` True

  it "CnstrT includes Transfer" $ do
    let ann = TA Set.empty (TagExpr Set.empty (Set.singleton "p"))
        delta = Map.empty
        cs = cnstrT ann delta 1
    any (\(ACnstr a _ _ _) -> a == Transfer) (Set.toList cs) `shouldBe` True

  it "CnstrU on non-empty annotation includes only Use" $ do
    let ann = TA Set.empty (TagExpr Set.empty (Set.singleton "p"))
        delta = Map.empty
        cs = cnstrU ann delta 0
    Set.map acAction cs `shouldBe` Set.singleton Use
