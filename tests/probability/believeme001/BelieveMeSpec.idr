module BelieveMeSpec

import Data.Bounded
import Data.Vect

import Hedgehog

import Statistics.Probability

probabilityCorrect : Probability -> PropertyT ()
probabilityCorrect p = do
  annotateShow p
  assert $ 0 <= p.asDouble && p.asDouble <= 1

moderateNat : Gen Nat
moderateNat = choice $
  [ element [0, 1, 2]
  , cast <$> bits64 constantBounded
  ]

ratio_correct_prop : Property
ratio_correct_prop = property $ do
  num      <- forAll moderateNat
  denDelta <- forAll moderateNat
  let (den ** lte) : (x : Nat ** num `LTE` x) := (num + denDelta ** lteAddRight num)
  let (den ** (lte, succ)) : (x : Nat ** (num `LTE` x, IsSucc x)) := case den of
                                                                       Z   => (S Z ** (lteSuccRight lte, ItIsSucc))
                                                                       S k => (S k ** (lte             , ItIsSucc))
  probabilityCorrect $ ratio num den @{lte} @{succ}

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("ratio", ratio_correct_prop)
      ]
  ]
