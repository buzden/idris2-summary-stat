module BelieveMeSpec

import Hedgehog

import Statistics.Erf

import Test.Common

erfc_bounds_corr : Property
erfc_bounds_corr = property $ do
  inp <- forAll anySolidDouble
  boundedDoubleCorrect $ erfc inp

invnormcdf_corr : Property
invnormcdf_corr = property $ do
  inp <- forAll anyProbability
  boundedDoubleCorrect $ invnormcdf inp

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("erfc bounds", erfc_bounds_corr)
      , ("invnormcdf", invnormcdf_corr)
      ]
  ]
