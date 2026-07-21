module EvalTest where

import qualified Data.Map.Strict as Map
import Test.Hspec

import TTpaola.Consent (RTag (..))
import TTpaola.Eval
import TTpaola.Runtime (TaggedVal (..), Value (..))
import TTpaola.Syntax

spec :: Spec
spec = describe "TTpaola.Eval" $ do
  it "evaluates literals" $ do
    evalVE Map.empty (VLitInt 3) `shouldBe` Right (TaggedVal (VInt_ 3) RTagEmpty)

  it "evaluates field lookup" $ do
    let phi = Map.singleton "x" (TaggedVal (VInt_ 1) RTagEmpty)
    evalVE phi (VField "x") `shouldBe` Right (TaggedVal (VInt_ 1) RTagEmpty)
