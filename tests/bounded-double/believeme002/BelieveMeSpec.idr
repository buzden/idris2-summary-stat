module BelieveMeSpec

import Data.Double.Bounded

import Hedgehog

import Test.Common

binop_corr : {f, g : (l, u, l', u' : Double) -> Double} ->
             (forL, forR : Gen (l ** u ** DoubleBetween l u)) ->
             ({l, u, l', u' : _} -> DoubleBetween l u -> DoubleBetween l' u' -> DoubleBetween (f l u l' u') (g l u l' u')) ->
             Property
binop_corr forL forR op = property $ do
  (_ ** _ ** x) <- forAll forL
  (_ ** _ ** y) <- forAll forR
  boundedDoubleCorrect $ x `op` y

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("(+)", binop_corr someBoundedDouble someBoundedDouble (+))
      , ("(-)", binop_corr someBoundedDouble someBoundedDouble (-))
      , ("(*)", binop_corr someBoundedDouble someBoundedDouble (*))
      , ("(/)", binop_corr someBoundedDouble nzBoundedDouble $ \x, y => (x / y) @{believe_me Oh})
      ]
  ]
