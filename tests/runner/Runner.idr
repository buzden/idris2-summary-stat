module Runner

import BaseDir

import Test.Golden.RunnerHelper

RunScriptArg where
  runScriptArg = baseTestsDir ++ "/.pack_lock"

main : IO ()
main = goldenRunner
  [ "Error function" `atDir` "error-function"
  , "Probability type" `atDir` "probability"
  , "Confidence interval" `atDir` "confidence-interval"
  ]
