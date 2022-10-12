module Spec

import Data.Double.Bounded

import Hedgehog

import Test.Common

numericDouble_gen_corr : Property
numericDouble_gen_corr = property $ do
  (canNegInf, canPosInf) <- forAll [| (bool, bool) |]
  x <- forAll $ numericDouble canNegInf canPosInf
  assert $ x == x
  assert $ not canNegInf `implies` x /= NegInf
  assert $ not canPosInf `implies` x /= PosInf

nonNegativeDouble_gen_corr : Property
nonNegativeDouble_gen_corr = property $ do
  canPosInf <- forAll bool
  x <- forAll $ nonNegativeDouble canPosInf
  assert $ x == x
  assert $ x >= 0
  assert $ not canPosInf `implies` x /= PosInf

anySolidDouble_gen_corr : Property
anySolidDouble_gen_corr = property $ do
  x <- forAll anySolidDouble
  boundedDoubleCorrect x

anyBoundedDouble_gen_corr : Property
anyBoundedDouble_gen_corr = property $ do
  l <- forAll $ numericDouble True True
  u <- forAll $ numericDouble True True
  x <- forAll $ anyBoundedDouble (l `min` u) (l `max` u) @{believe_me Oh}
  boundedDoubleCorrect x

someBoundedDouble_gen_corr : Property
someBoundedDouble_gen_corr = property $ do
  (_ ** _ ** x) <- forAll someBoundedDouble
  boundedDoubleCorrect x

main : IO ()
main = test
  [ "double generators" `MkGroup`
      [ ("numericDouble", numericDouble_gen_corr)
      , ("nonNegativeDouble", nonNegativeDouble_gen_corr)
      ]
  , "bounded double generators" `MkGroup`
      [ ("anySolidDouble", anySolidDouble_gen_corr)
      , ("anyBoundedDouble", anyBoundedDouble_gen_corr)
      , ("someBoundedDouble", someBoundedDouble_gen_corr)
      ]
  ]
