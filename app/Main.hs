module Main where

import TyPAOL.Examples.FoodDelivery (foodDelivery)
import TyPAOL.Runtime (buildClassTable, initConfig)
import TyPAOL.TypeChecker (inferMethodMeta)

main :: IO ()
main = do
  let ct0 = buildClassTable foodDelivery
  case inferMethodMeta ct0 of
    Left err -> print err
    Right ct -> print (initConfig foodDelivery ct)
