module BelieveMeSpec

import Data.Bounded
import Data.Vect

import Hedgehog

import Statistics.Probability

import Test.Common

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

double_div_correct_prop : Property
double_div_correct_prop = property $ do
  num <- forAll $ double $ exponentialDouble 1 MaxDouble
  let num = if num == 1 then 1.000001 else num -- no filtration in this port :-(
  den <- forAll $ double $ exponentialDouble num MaxDouble
  let Yes prf = decSo _
    | No _ => annotate "\{show num} / \{show den}" >> failure
  probabilityCorrect $ FromDoubles.(/) num den @{prf}

fromInteger_correct_prop : Property
fromInteger_correct_prop = property $ do
  (n ** prf) <- forAll $ element [(0 ** Left Refl), (1 ** Right Refl)]
  probabilityCorrect $ fromInteger n @{prf}
  where
    implementation {0 f : Integer -> Type} -> Show (x : Integer ** f x) where
      show (x ** _) = show x

main : IO ()
main = test
  [ "believe_me" `MkGroup`
      [ ("ratio", ratio_correct_prop)
      , ("doubles (/)", double_div_correct_prop)
      , ("fromInteger", fromInteger_correct_prop)
      ]
  ]
