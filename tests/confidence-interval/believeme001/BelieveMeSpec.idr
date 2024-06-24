module BelieveMeSpec

import Hedgehog

import Statistics.Confidence
import Statistics.Norm.Rough
import Statistics.Norm.Precise

import Test.Common

MaxWilsonCount : Nat
MaxWilsonCount = 1000000

wilsonBounds_corr : InvNormCDF => Property
wilsonBounds_corr = property $ do
  confidence <- forAll anyProbability
  count' <- forAll $ nat $ constant 0 MaxWilsonCount
  successes <- forAll anyProbability
  let wb@(low, high) = wilsonBounds confidence (S count') successes
  annotateShow wb
  probabilityCorrect low
  probabilityCorrect high

coverBetween_corr : Property
coverBetween_corr = property $ do
  tolerance <- forAll $ choice [pure DefaultTolerance, anyProbability]
  oneP      <- forAll anyProbability
  anotherP  <- forAll anyProbability
  let condition : Nat -> Bool := const False -- particular function does not really matter
  let coverageTest = coverBetween {tolerance} oneP anotherP condition
  annotate "\{show coverageTest.minimalProbability} <= \{show coverageTest.maximalProbability}"
  assert $ coverageTest.minimalProbability <= coverageTest.maximalProbability

  let %hint e : Eps; e = MkEps $ 1.0e-15 `max` tolerance.inv.asDouble
  let (mi, ma) = (min oneP anotherP, max oneP anotherP)
  diff coverageTest.minimalProbability eqUpToEps mi
  diff coverageTest.maximalProbability eqUpToEps ma

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("wilsonBounds", wilsonBounds_corr)
      , ("wilsonBounds @{Rough}", wilsonBounds_corr @{Rough})
      , ("coverBetween", coverBetween_corr)
      ]
  ]
