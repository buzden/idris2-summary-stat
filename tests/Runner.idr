module Runner

import Data.String

import Test.Golden

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

testOptions : Options
testOptions = {timing := True, interactive := True} (initOptions "idris2" True)

main : IO ()
main = runnerWith testOptions $
  [ !("Bounded Double" `atDir` "bounded-double")
  , !("Error function" `atDir` "error-function")
  , !("Probability type" `atDir` "probability")
  , !("Confidence interval" `atDir` "confidence-interval")
  ]
