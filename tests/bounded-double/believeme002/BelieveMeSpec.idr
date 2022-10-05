module BelieveMeSpec

import Data.Double.Bounded

import Hedgehog

boundedDoubleCorrect : {l, u : _} -> DoubleBetween l u -> PropertyT ()
boundedDoubleCorrect x = do
  annotate "\{show l} <= \{show x} <= \{show u}"
  assert $ l <= x.asDouble && x.asDouble <= u

MaxDouble, MinDouble, ClosestToZero : Double
MaxDouble = 1.79769e+308
MinDouble = -MaxDouble
ClosestToZero = 2.22507e-308

numericDouble : Gen Double
numericDouble = double $ exponentialDoubleFrom 0 MinDouble MaxDouble

boundedDouble : Gen (l ** u ** DoubleBetween l u)
boundedDouble = do
  l <- numericDouble
  u <- numericDouble
  let (l, u) = (min l u, max l u)
  x <- double $ exponentialDouble l u
  pure (l ** u ** BoundedDouble x @{believe_me Oh} @{believe_me Oh})

boundedDouble_gen_corr : Property
boundedDouble_gen_corr = property $ do
  (_ ** _ ** x) <- forAll boundedDouble
  boundedDoubleCorrect x

nzBoundedDouble : Gen (l ** u ** DoubleBetween l u)
nzBoundedDouble = do
  l <- numericDouble
  let l = if l == 0 then -ClosestToZero else l
  u <- numericDouble
  let u = if u == 0 then ClosestToZero else u
  let (l, u) = (min l u, max l u)
  x <- double $ exponentialDouble l u
  let x = if x == 0 then ClosestToZero else x
  pure (l ** u ** BoundedDouble x @{believe_me Oh} @{believe_me Oh})

nzBoundedDouble_gen_corr : Property
nzBoundedDouble_gen_corr = property $ do
  (_ ** _ ** x) <- forAll nzBoundedDouble
  boundedDoubleCorrect x

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
      [ ("bd gen", boundedDouble_gen_corr)
      , ("nzbd gen", nzBoundedDouble_gen_corr)
      , ("(+)", binop_corr boundedDouble boundedDouble (+))
      , ("(-)", binop_corr boundedDouble boundedDouble (-))
      , ("(*)", binop_corr boundedDouble boundedDouble (*))
      , ("(/)", binop_corr boundedDouble nzBoundedDouble $ \x, y => (x / y) @{believe_me Oh})
      ]
  ]
