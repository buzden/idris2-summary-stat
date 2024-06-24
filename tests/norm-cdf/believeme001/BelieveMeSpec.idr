module BelieveMeSpec

import Hedgehog

import Statistics.Norm.Precise
import Statistics.Norm.Rough

import Test.Common

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("invnormcdf", un_corr invnormcdf)
      , ("invnormcdf @{Rough}", un_corr $ invnormcdf @{Rough})
      ]
  ]
