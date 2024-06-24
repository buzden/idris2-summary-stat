module InversionSpec

import Hedgehog

import Statistics.Norm.Precise
import Statistics.Norm.Rough

import Test.Common

namespace Forward

  domainLimit : Double
  domainLimit = 3

  inormDouble : Gen SolidDouble
  inormDouble = relaxToSolid <$> anyBoundedDouble (-domainLimit) domainLimit

  export
  normcdf_inv_corr : Eps => InvNormCDF => Property
  normcdf_inv_corr = property $ do
    x <- forAll inormDouble
    annotateShow $ normcdf x
    diff (invnormcdf $ normcdf x) eqUpToEps x

namespace Backward

  export
  inv_normcdf_corr : Eps => InvNormCDF => Property
  inv_normcdf_corr = property $ do
    x <- forAll anyProbability
    diff (normcdf $ invnormcdf x) eqUpToEps x

main : IO ()
main = test
  [ "inversions" `MkGroup`
      [ ("normcdf", normcdf_inv_corr @{MkEps 1.0e-11})
      , ("normcdf @{Rough}", normcdf_inv_corr  @{MkEps 1.0e-8} @{Rough})
      ]
  , "anti-inversions" `MkGroup`
      [ ("normcdf", inv_normcdf_corr @{MkEps 1.0e-15})
      , ("normcdf @{Rough}", inv_normcdf_corr  @{MkEps 1.0e-9} @{Rough})
      ]
  ]
