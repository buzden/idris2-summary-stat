module Runner

import Data.String

import Test.Golden

import System.Directory
import System.File

atDir : (poolName : String) -> (dir : String) -> IO TestPool
atDir poolName dir = do
  True <- exists dir
    | False => emptyPool
  Right (_::_) <- listDir dir
    | _ => emptyPool
  testsInDir dir (not . isPrefixOf "_") poolName [] Nothing

  where
    emptyPool : IO TestPool
    emptyPool = pure $ MkTestPool poolName [] Nothing []

testOptions : Options
testOptions = {timing := True, interactive := True} (initOptions "idris2" True)

main : IO ()
main = runnerWith testOptions $
  [ !("Bounded Double" `atDir` "bounded-double")
  , !("Error function" `atDir` "error-function")
  , !("Probability type" `atDir` "probability")
  , !("Confidence interval" `atDir` "confidence-interval")
  ]
