module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Error function" `atDir` "error-function"
  , "Probability type" `atDir` "probability"
  , "Confidence interval" `atDir` "confidence-interval"
  ]
