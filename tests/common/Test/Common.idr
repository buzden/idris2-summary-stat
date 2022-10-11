module Test.Common

import Data.Buffer
import Data.Bounded
import Data.Double.Bounded
import Data.Vect

import Hedgehog

import Statistics.Probability

%default total

public export
implies : Bool -> Bool -> Bool
implies a c = not a || c

public export
MaxDouble, MinDouble, ClosestToZero, PosInf, NegInf : Double
MaxDouble = 1.79769e+308
MinDouble = -MaxDouble
ClosestToZero = 2.22507e-308
PosInf = 1.0/0
NegInf = -1.0/0

export
probabilityCorrect : Probability -> PropertyT ()
probabilityCorrect p = do
  annotateShow p
  assert $ 0 <= p.asDouble && p.asDouble <= 1

export
veryAnyDouble : Gen Double
veryAnyDouble = unsafePerformIO . doubleFromBits64 <$> bits64 constantBounded
  where
    doubleFromBits64 : HasIO io => Bits64 -> io Double
    doubleFromBits64 n = do
      Just bf <- newBuffer 8
        | Nothing => pure $ 0.0/0
      setBits64 bf 0 n
      getDouble bf 0

export
anySolidDouble : Gen SolidDouble
anySolidDouble = veryAnyDouble >>= \x => case (decSo $ NegInf <= x, decSo $ x <= PosInf) of
  (Yes lp, Yes rp) => pure $ BoundedDouble x
  _                => element [0, ClosestToZero, MinDouble, MaxDouble, NegInf, PosInf] <&> \x => BoundedDouble x @{believe_me Oh} @{believe_me Oh}

export
boundedDoubleCorrect : {l, u : _} -> DoubleBetween l u -> PropertyT ()
boundedDoubleCorrect x = do
  annotate "\{show l} <= \{show x} <= \{show u}"
  assert $ l <= x.asDouble && x.asDouble <= u

export
numericDouble : Gen Double
numericDouble = map purify $ double $ exponentialDoubleFrom 0 MinDouble MaxDouble
  where
    purify : Double -> Double
    purify x = if x == 1.0/0 || x == (-1.0)/0 || not (x == x) then 0 else x

export
someBoundedDouble : Gen (l ** u ** DoubleBetween l u)
someBoundedDouble = do
  l <- numericDouble
  u <- numericDouble
  let (l, u) = (min l u, max l u)
  x <- double $ exponentialDouble l u
  pure (l ** u ** BoundedDouble x @{believe_me Oh} @{believe_me Oh})

-- Bounded double with non-zero bounds and non-zero value
export
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
