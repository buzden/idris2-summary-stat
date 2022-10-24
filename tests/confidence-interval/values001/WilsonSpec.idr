module WilsonSpec

import Data.DPair

import Hedgehog
import Hedgehog.Internal.Property.Hack

import Statistics.Confidence

import Test.Common

MaxCount : Nat
MaxCount = 1000000000000

AcceptanceTolerance : Double
AcceptanceTolerance = 1.0e-15

wilsonBounds_asHedgehog : Property
wilsonBounds_asHedgehog = property $ do
  count      <- forAll $ nat $ constant 1 MaxCount
  positives  <- forAll $ nat $ constant 0 count
  let toAcc : Double -> Double
      toAcc p = if p < AcceptanceTolerance then AcceptanceTolerance
                   else if p > 1 - AcceptanceTolerance then 1 - AcceptanceTolerance
                   else p
  acceptance <- forAll $ toAcc . (.asDouble) <$> anyProbability

  let fromHedgehog : (Double, Double) =
    wilsonBounds' positives count $ Element acceptance $ believe_me $ Refl {x=Z}

  let fromSummaryStat : (Double, Double) = mapHom (.asDouble) $ wilsonBounds
                                             (P $ BoundedDouble acceptance @{believe_me Oh} @{believe_me Oh})
                                             count
                                             (ratio positives count @{believe_me LTEZero} @{believe_me ItIsSucc})
                                             @{believe_me ItIsSucc}

  annotate "from Hedgehog: \{show fromHedgehog}"
  annotate "from summary-stat: \{show fromSummaryStat}"

  let %hint
      e : Eps
      e = MkEps $ 1.0e-15 `max` acceptance

  diff (fst fromHedgehog) eqUpToEps (fst fromSummaryStat)
  diff (snd fromHedgehog) eqUpToEps (snd fromSummaryStat)

wilsonBounds_low_leq_high : Property
wilsonBounds_low_leq_high = property $ do
  count      <- forAll $ nat $ constant 1 MaxCount
  positives  <- forAll $ nat $ constant 0 count
  let toAcc : Double -> Double
      toAcc p = if p < AcceptanceTolerance then AcceptanceTolerance
                   else if p > 1 - AcceptanceTolerance then 1 - AcceptanceTolerance
                   else p
  acceptance <- forAll $ toAcc . (.asDouble) <$> anyProbability

  let (lo, hi) : (Double, Double) = mapHom (.asDouble) $ wilsonBounds
                                      (P $ BoundedDouble acceptance @{believe_me Oh} @{believe_me Oh})
                                      count
                                      (ratio positives count @{believe_me $ LTEZero {right=Z}} @{believe_me $ ItIsSucc {n=1}})
                                      @{believe_me $ ItIsSucc {n=1}}

  annotate "from summary-stat: \{show (lo, hi)}"

  assert $ lo <= hi

main : IO ()
main = test
  [ "Wilson bounds" `MkGroup`
      [ ("as in hedgehog", wilsonBounds_asHedgehog)
      , ("low <= high", wilsonBounds_low_leq_high)
      ]
  ]
