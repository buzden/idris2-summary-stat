module Tests

import Test.Golden.RunnerHelper

main : IO ()
main = goldenRunner
  [ "Error function" `atDir` "error-function"
  , "Normal distribution CDF" `atDir` "norm-cdf"
  , "Probability type" `atDir` "probability"
  , "Confidence interval" `atDir` "confidence-interval"
  ]
