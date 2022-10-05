module Spec

import Data.Double.Bounded

import Hedgehog

import Test.Common

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
      [ ("someBoundedDouble", someBoundedDouble_gen_corr)
      , ("nzBoundedDouble", nzBoundedDouble_gen_corr)
      ]
  ]
