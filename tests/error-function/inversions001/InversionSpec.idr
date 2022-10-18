module InversionSpec

import Hedgehog

import Statistics.Erf

import Test.Common

namespace Forward

  %hint
  e : Eps
  e = MkEps 1.0e-11

  domainLimit : Double
  domainLimit = 3

  erfDouble : Gen SolidDouble
  erfDouble = relaxToSolid <$> anyBoundedDouble (-domainLimit) domainLimit

  export
  erf_inv_corr : Property
  erf_inv_corr = property $ do
    x <- forAll erfDouble
    annotateShow $ erf x
    diff (inverf $ erf x) eqUpToEps x

  export
  erfc_inv_corr : Property
  erfc_inv_corr = property $ do
    x <- forAll erfDouble
    annotateShow $ erfc x
    diff (inverfc $ erfc x) eqUpToEps x

  export
  normcdf_inv_corr : Property
  normcdf_inv_corr = property $ do
    x <- forAll erfDouble
    annotateShow $ normcdf x
    diff (invnormcdf $ normcdf x) eqUpToEps x

namespace Backward

  %hint
  e : Eps
  e = MkEps 1.0e-15

  export
  inv_erf_corr : Property
  inv_erf_corr = property $ do
    x <- forAll $ anyBoundedDouble _ _
    diff (erf $ inverf x) eqUpToEps x

  export
  inv_erfc_corr : Property
  inv_erfc_corr = property $ do
    x <- forAll $ anyBoundedDouble _ _
    diff (erfc $ inverfc x) eqUpToEps x

  export
  inv_normcdf_corr : Property
  inv_normcdf_corr = property $ do
    x <- forAll anyProbability
    diff (normcdf $ invnormcdf x) eqUpToEps x

main : IO ()
main = test
  [ "inversions" `MkGroup`
      [ ("erf", erf_inv_corr)
      , ("erfc", erfc_inv_corr)
      , ("normcdf", normcdf_inv_corr)
      ]
  , "anti-inversions" `MkGroup`
      [ ("erf", inv_erf_corr)
      , ("erfc", inv_erfc_corr)
      , ("normcdf", inv_normcdf_corr)
      ]
  ]
