module BelieveMeSpec

import Data.Double.Bounded

import Hedgehog

import Test.Common

nat_cast_corr : Property
nat_cast_corr = property $ do
  n <- forAll somewhatNat
  boundedDoubleCorrect $ cast n {to=DoubleBetween 0 PosInf}

integer_cast_corr : Property
integer_cast_corr = property $ do
  n <- forAll somewhatInteger
  boundedDoubleCorrect $ cast n {to=SolidDouble}

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("cast from nat",     nat_cast_corr)
      , ("cast from integer", integer_cast_corr)
      ]
  ]
