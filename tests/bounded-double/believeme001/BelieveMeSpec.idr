module BelieveMeSpec

import Data.Buffer
import Data.Bounded
import Data.Double.Bounded

import Hedgehog

import Test.Common

lteRefl_prop : Property
lteRefl_prop = property $ do
  x <- forAll veryAnyDouble
  assert $ x == x `implies` x <= x

lteNotNaNL_prop : Property
lteNotNaNL_prop = property $ do
  x <- forAll veryAnyDouble
  y <- forAll veryAnyDouble
  assert $ x <= y `implies` x == x

lteNotNaNR_prop : Property
lteNotNaNR_prop = property $ do
  x <- forAll veryAnyDouble
  y <- forAll veryAnyDouble
  assert $ y <= x `implies` x == x

lteTrans_prop : Property
lteTrans_prop = property $ do
  x <- forAll veryAnyDouble
  y <- forAll veryAnyDouble
  z <- forAll veryAnyDouble
  assert $ (x <= y && y <= z) `implies` x <= z
  -- very ineffective check...

lteNegInf_prop : Property
lteNegInf_prop = property $ do
  x <- forAll veryAnyDouble
  assert $ x == x `implies` NegInf <= x

ltePosInf_prop : Property
ltePosInf_prop = property $ do
  x <- forAll veryAnyDouble
  assert $ x == x `implies` x <= PosInf

zormin_prop : Property
zormin_prop = property $ do
  l <- forAll $ numericDouble True True
  u <- forAll $ numericDouble True True
  let z = zormin l u
  annotateShow z
  assert $ z == 0 || z == l || z == u
  assert $ l <= 0 && 0 <= u `implies` z == 0

main : IO ()
main = test
  [ "believe_me lte" `MkGroup`
      [ ("lteRefl", lteRefl_prop)
      , ("lteNotNaNL", lteNotNaNL_prop )
      , ("lteNotNaNR", lteNotNaNR_prop )
      , ("lteTrans", lteTrans_prop)
      , ("lteNegInf", lteNegInf_prop)
      , ("ltePosInf", ltePosInf_prop)
      ]
  , "aux doubles funs" `MkGroup`
      [ ("zormin", zormin_prop)
      ]
  ]
