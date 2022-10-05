module BelieveMeSpec

import Data.Buffer
import Data.Bounded

import Hedgehog

import Test.Common

lteRefl_prop : Property
lteRefl_prop = property $ do
  x <- forAll veryAnyDouble
  annotateShow x
  assert $ x == x `implies` x <= x

lteTrans_prop : Property
lteTrans_prop = property $ do
  x <- forAll veryAnyDouble
  y <- forAll veryAnyDouble
  z <- forAll veryAnyDouble
  assert $ (x <= y && y <= z) `implies` x <= z
  -- very ineffective check...

main : IO ()
main = test
  [ "believe_me lte" `MkGroup`
      [ ("lteRefl", lteRefl_prop)
      , ("lteTrans", lteTrans_prop)
      ]
  ]
