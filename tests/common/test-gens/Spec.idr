module Spec

import Data.Double.Bounded

import Hedgehog

import Test.Common

numericDouble_gen_corr : Property
numericDouble_gen_corr = property $ do
  x <- forAll numericDouble
  annotateShow x
  assert $ x == x && x /= (1/0) && x /= (-1/0)

someBoundedDouble_gen_corr : Property
someBoundedDouble_gen_corr = property $ do
  (_ ** _ ** x) <- forAll someBoundedDouble
  boundedDoubleCorrect x

nzBoundedDouble_gen_corr : Property
nzBoundedDouble_gen_corr = property $ do
  (_ ** _ ** x) <- forAll nzBoundedDouble
  boundedDoubleCorrect x

main : IO ()
main = test
  [ "common generators" `MkGroup`
      [ ("numericDouble", numericDouble_gen_corr)
      , ("someBoundedDouble", someBoundedDouble_gen_corr)
      , ("nzBoundedDouble", nzBoundedDouble_gen_corr)
      ]
  ]
