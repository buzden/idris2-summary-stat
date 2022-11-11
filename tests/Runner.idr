module Runner

import BaseDir

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Common facilities" `atDir` "common"
  , "Bounded Double" `atDir` "bounded-double"
  , "Error function" `atDir` "error-function"
  , "Probability type" `atDir` "probability"
  , "Confidence interval" `atDir` "confidence-interval"
  ]
