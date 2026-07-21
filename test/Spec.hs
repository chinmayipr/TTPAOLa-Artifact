module Main where

import Test.Hspec

import qualified ConsentTest
import qualified EvalTest
import qualified InterpreterTest
import qualified LitmusTest
import qualified MigrationTest
import qualified SafetyTest
import qualified TypeCheckerTest

main :: IO ()
main =
  hspec $ do
    ConsentTest.spec
    EvalTest.spec
    InterpreterTest.spec
    TypeCheckerTest.spec
    MigrationTest.spec
    SafetyTest.spec
    LitmusTest.spec
