module BelieveMeSpec

import Hedgehog

import Statistics.Confidence

import Test.Common

MaxWilsonCount : Nat
MaxWilsonCount = 1000000

wilsonBounds_corr : Property
wilsonBounds_corr = property $ do
  confidence <- forAll anyProbability
  count' <- forAll $ nat $ constant 0 MaxWilsonCount
  successes <- forAll anyProbability
  let wb@(low, high) = wilsonBounds confidence (S count') successes
  annotateShow wb
  probabilityCorrect low
  probabilityCorrect high

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("wilsonBounds", wilsonBounds_corr)
      ]
  ]
