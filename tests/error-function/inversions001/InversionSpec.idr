module InversionSpec

import Hedgehog

import Statistics.Erf
import Statistics.Norm.Precise
import Statistics.Norm.Rough

import Test.Common

namespace Forward

  domainLimit : Double
  domainLimit = 3

  erfDouble : Gen SolidDouble
  erfDouble = relaxToSolid <$> anyBoundedDouble (-domainLimit) domainLimit

  export
  erf_inv_corr : InvNormCDF => Eps => Property
  erf_inv_corr = property $ do
    x <- forAll erfDouble
    annotateShow $ erf x
    diff (inverf $ erf x) eqUpToEps x

  export
  erfc_inv_corr : InvNormCDF => Eps => Property
  erfc_inv_corr = property $ do
    x <- forAll erfDouble
    annotateShow $ erfc x
    diff (inverfc $ erfc x) eqUpToEps x

namespace Backward

  export
  inv_erf_corr : InvNormCDF => Eps => Property
  inv_erf_corr = property $ do
    x <- forAll $ anyBoundedDouble _ _
    diff (erf $ inverf x) eqUpToEps x

  export
  inv_erfc_corr : InvNormCDF => Eps => Property
  inv_erfc_corr = property $ do
    x <- forAll $ anyBoundedDouble _ _
    diff (erfc $ inverfc x) eqUpToEps x

main : IO ()
main = test
  [ "inversions" `MkGroup` let %hint e : Eps; e = MkEps 1.0e-11 in
      [ ("erf", erf_inv_corr)
      , ("erfc", erfc_inv_corr)
      ]
  , "anti-inversions" `MkGroup` let %hint e : Eps; e = MkEps 1.0e-15 in
      [ ("erf", inv_erf_corr)
      , ("erfc", inv_erfc_corr)
      ]
  , "inversions @{Rough}" `MkGroup` let %hint e : Eps; e = MkEps 1.0e-8 in
      [ ("erf", erf_inv_corr @{Rough})
      , ("erfc", erfc_inv_corr @{Rough})
      ]
  , "anti-inversions @{Rough}" `MkGroup` let %hint e : Eps; e = MkEps 1.0e-9 in
      [ ("erf", inv_erf_corr @{Rough})
      , ("erfc", inv_erfc_corr @{Rough})
      ]
  ]
