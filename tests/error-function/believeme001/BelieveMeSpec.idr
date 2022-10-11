module BelieveMeSpec

import Hedgehog

import Statistics.Erf

import Test.Common

erfc_bounds_corr : Property
erfc_bounds_corr = property $ do
  inp <- forAll veryAnyDouble
  boundedDoubleCorrect $ erfc inp

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("erfc bounds", erfc_bounds_corr)
      ]
  ]
