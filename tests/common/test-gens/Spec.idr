module Spec

import Data.Double.Bounded

import Hedgehog

import Test.Common

numericDouble_gen_corr : Property
numericDouble_gen_corr = property $ do
  (canNegInf, canPosInf) <- forAll [| (bool, bool) |]
  x <- forAll $ numericDouble canNegInf canPosInf
  assert $ x == x
  assert $ not canNegInf `implies` x /= NegInf
  assert $ not canPosInf `implies` x /= PosInf

anySolidDouble_gen_corr : Property
anySolidDouble_gen_corr = property $ do
  x <- forAll anySolidDouble
  boundedDoubleCorrect x

someBoundedDouble_gen_corr : Property
someBoundedDouble_gen_corr = property $ do
  (_ ** _ ** x) <- forAll someBoundedDouble
  boundedDoubleCorrect x

main : IO ()
main = test
  [ "common generators" `MkGroup`
      [ ("numericDouble", numericDouble_gen_corr)
      , ("anySolidDouble", anySolidDouble_gen_corr)
      , ("someBoundedDouble", someBoundedDouble_gen_corr)
      ]
  ]
