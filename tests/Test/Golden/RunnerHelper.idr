module Test.Golden.RunnerHelper

import Data.Maybe
import Data.String

import public Test.Golden

import System
import System.Directory

--- Options management ---

fitsPattern : (pattern, test : String) -> Bool
fitsPattern = isInfixOf

testOptions : {default "idris2" cmdUnderTest : String} -> IO Options
testOptions = do
  onlies <- filter (not . null) . tail' <$> getArgs
  pure $
    { color := True
    , timing := True
    , interactive := !((Just "true" /=) <$> getEnv "CI")
    , failureFile := Just "failures"
    , onlyNames := onlies <&> \patterns, test => any (`fitsPattern` test) patterns
    } (initOptions cmdUnderTest True)

--- Base dir facilities ---

public export
interface BaseTestsDir where
  constructor MkBaseTestsDir
  baseTestsDir : String

--- A universal way to set test pools from different origins ---

export
interface TestPoolLike a where
  toTestPool : a -> IO TestPool

export
TestPoolLike (IO TestPool) where
  toTestPool = id

export
TestPoolLike TestPool where
  toTestPool = pure

public export
data TestPools : Type where
  Nil  : TestPools
  (::) : TestPoolLike a => a -> TestPools -> TestPools

toList : TestPools -> List $ IO TestPool
toList []      = []
toList (x::xs) = toTestPool x :: toList xs

--- Facilities for user's convenience ---

export
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

--- Toplevel running ---

export
goldenRunner : BaseTestsDir => TestPools -> IO ()
goldenRunner tps = do
  ignore $ changeDir baseTestsDir
  runnerWith !testOptions !(sequence $ toList tps)
