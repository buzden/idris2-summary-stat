module BelieveMeSpec

import Data.Buffer
import Data.Bounded

import Hedgehog

doubleFromBits64 : HasIO io => Bits64 -> io Double
doubleFromBits64 n = do
  Just bf <- newBuffer 8
    | Nothing => pure $ 0.0/0
  setBits64 bf 0 n
  getDouble bf 0

veryAnyDouble : Gen Double
veryAnyDouble = unsafePerformIO . doubleFromBits64 <$> bits64 constantBounded

implies : Bool -> Bool -> Bool
implies a c = not a || c

lteRefl_prop : Property
lteRefl_prop = property $ do
  x <- forAll veryAnyDouble
  annotateShow x
  assert $ x == x `implies` x <= x

lteTrans_prop : Property
lteTrans_prop = property $ do
  x <- forAll veryAnyDouble
  y <- forAll veryAnyDouble
  z <- forAll veryAnyDouble
  assert $ (x <= y && y <= z) `implies` x <= z
  -- very ineffective check...

main : IO ()
main = test
  [ "believe_me lte" `MkGroup`
      [ ("lteRefl", lteRefl_prop)
      , ("lteTrans", lteTrans_prop)
      ]
  ]
