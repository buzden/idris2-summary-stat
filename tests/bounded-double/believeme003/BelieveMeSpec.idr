module BelieveMeSpec

import Data.Double.Bounded

import Hedgehog

import Test.Common

pol_corr : {f, g : _} -> (forall l, u. DoubleBetween l u -> DoubleBetween (f l) (g u)) -> Property
pol_corr fn = property $ do
  (l ** u ** x) <- forAll someBoundedDouble
  boundedDoubleCorrect $ fn x

pol_nneg_corr : {f, g : _} -> (forall l, u. (0 _ : So $ 0 <= l) => DoubleBetween l u -> DoubleBetween (f l) (g u)) -> Property
pol_nneg_corr fn = property $ do
  l <- forAll $ nonNegativeDouble True
  u <- forAll $ nonNegativeDouble True
  let (l, u) = (min l u, max l u)
  x <- forAll $ anyBoundedDouble l u @{believe_me Oh}
  boundedDoubleCorrect $ fn x @{believe_me Oh}

un_corr : {l, u, l', u' : _} -> (0 _ : So $ l <= u) => (DoubleBetween l u -> DoubleBetween l' u') -> Property
un_corr f = property $ do
  inp <- forAll $ anyBoundedDouble l u
  boundedDoubleCorrect $ f inp

main : IO ()
main = test
  [ "believe_me poly bounds" `MkGroup`
      [ ("sqrt",        pol_nneg_corr sqrt)
      , ("sqrtRelaxed", pol_nneg_corr sqrtRelaxed)
      , ("log",         pol_nneg_corr log)
      , ("exp",         pol_corr exp)
      , ("expRelaxed",  pol_corr expRelaxed)
      ]
  , "believe_me const bounds" `MkGroup`
      [ ("sin",  un_corr sin)
      , ("cos",  un_corr cos)
      , ("asin", un_corr asin)
      , ("acos", un_corr acos)
      ]
  ]
