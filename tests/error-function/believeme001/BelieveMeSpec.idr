module BelieveMeSpec

import Hedgehog

import Statistics.Erf
import Statistics.Norm.Precise
import Statistics.Norm.Rough

import Test.Common

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("erfc bounds", un_corr erfc)
      ]
  , "other bounds" `MkGroup`
      [ ("erf", un_corr erf)
      , ("inverfc", un_corr inverfc)
      , ("inverfc @{Rough}", un_corr $ inverfc @{Rough})
      , ("inverf", un_corr inverf)
      , ("inverf @{Rough}", un_corr $ inverf @{Rough})
      ]
  ]
