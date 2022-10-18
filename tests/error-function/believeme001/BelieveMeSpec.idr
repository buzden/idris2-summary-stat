module BelieveMeSpec

import Hedgehog

import Statistics.Erf

import Test.Common

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("erfc bounds", un_corr erfc)
      , ("invnormcdf", un_corr invnormcdf)
      ]
  , "other bounds" `MkGroup`
      [ ("erf", un_corr erf)
      , ("normcdf", un_corr normcdf)
      , ("inverfc", un_corr inverfc)
      , ("inverf", un_corr inverf)
      ]
  ]
