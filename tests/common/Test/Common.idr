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
numericDouble : (canNegInf, canPosInf : Bool) -> Gen Double
numericDouble canNegInf canPosInf = map purify $ double $ exponentialDoubleFrom 0 MinDouble MaxDouble
  where
    purify : Double -> Double
    purify x = if not canPosInf && x == PosInf
               || not canNegInf && x == NegInf
               || not (x == x)
               then 0 else x

export
someBoundedDouble : Gen (l ** u ** DoubleBetween l u)
someBoundedDouble = do
  l <- numericDouble True True
  u <- numericDouble True True
  let (l, u) = (min l u, max l u)
  let inBounds : Double -> Bool
      inBounds x = l <= x && x <= u
  let ifInBounds : Double -> Maybe Double
      ifInBounds x = if inBounds x then Just x else Nothing
  let basic : Gen Double
      basic = element $ reorder $ l :: u :: fromList (mapMaybe ifInBounds [0, ClosestToZero, MinDouble, MaxDouble, NegInf, PosInf])
  x <- choice
         [ basic
         , double (exponentialDouble (l `max` MinDouble) (u `min` MaxDouble)) >>= \x =>
             if inBounds x then pure x else basic
         ]
  pure (l ** u ** BoundedDouble x @{believe_me Oh} @{believe_me Oh})
  where
    reorder : forall k, a. Vect (S k) a -> Vect (S k) a
    reorder $ a::b::c::rest = c::a::b::rest
    reorder xs              = xs

-- Bounded double with non-zero bounds and non-zero value
export
nzBoundedDouble : Gen (l ** u ** DoubleBetween l u)
nzBoundedDouble = someBoundedDouble <&> \(l ** u ** x) => do
  let l = if l == 0 then -ClosestToZero else l
  let u = if u == 0 then ClosestToZero else u
  let x = x.asDouble
  let x = if x == 0 then ClosestToZero else x
  (l ** u ** BoundedDouble x @{believe_me Oh} @{believe_me Oh})
