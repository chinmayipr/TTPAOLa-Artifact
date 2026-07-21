module Main where

import TTpaola.Examples.FoodDelivery (foodDelivery)
import TTpaola.Runtime (buildClassTable, initConfig)
import TTpaola.TypeChecker (inferMethodMeta)

main :: IO ()
main = do
  let ct0 = buildClassTable foodDelivery
  case inferMethodMeta ct0 of
    Left err -> print err
    Right ct -> print (initConfig foodDelivery ct)
