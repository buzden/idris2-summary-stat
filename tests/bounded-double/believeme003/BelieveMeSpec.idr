module BelieveMeSpec

import Data.Double.Bounded

import Hedgehog

import Test.Common

un_corr : {l, u, l', u' : _} -> (0 _ : So $ l <= u) => (DoubleBetween l u -> DoubleBetween l' u') -> Property
un_corr f = property $ do
  inp <- forAll $ anyBoundedDouble l u
  boundedDoubleCorrect $ f inp

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("sqrt", un_corr sqrt)
      , ("log",  un_corr log)
      , ("exp",  un_corr exp)
      , ("sin",  un_corr sin)
      , ("cos",  un_corr cos)
      , ("asin", un_corr asin)
      , ("acos", un_corr acos)
      ]
  ]
