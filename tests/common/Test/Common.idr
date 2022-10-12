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
anyBoundedDouble : (l, u : Double) -> (0 _ : So $ l <= u) => Gen $ DoubleBetween l u
anyBoundedDouble l u = do
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
  pure $ BoundedDouble x @{believe_me Oh} @{believe_me Oh}
  where
    reorder : forall k, a. Vect (S k) a -> Vect (S k) a
    reorder $ a::b::c::rest = c::a::b::rest
    reorder xs              = xs

export
someBoundedDouble : Gen (l ** u ** DoubleBetween l u)
someBoundedDouble = do
  l <- numericDouble True True
  u <- numericDouble True True
  let (l, u) = (min l u, max l u)
  x <- anyBoundedDouble l u @{believe_me Oh}
  pure (l ** u ** x)

export
Show (So x) where
  show _ = "Oh"

--- Retry "filtration" facilities ---

public export
interface BuildableFrom from (0 what : from -> Type) where
  tryBuild : (f : from) -> Maybe $ what f

export
BuildableFrom f a => BuildableFrom f b => BuildableFrom f (\x => Either (a x) (b x)) where
  tryBuild x = Left <$> tryBuild x <|> Right <$> tryBuild x

export
BuildableFrom f a => BuildableFrom f b => BuildableFrom f (\x => (a x, b x)) where
  tryBuild x = [| (tryBuild x, tryBuild x) |]

export
{g : _} -> BuildableFrom f (So . g) where
  tryBuild x = case decSo $ g x of
                 Yes y => Just y
                 No _  => Nothing

export
plus : Gen a -> (0 b : _) -> BuildableFrom a b => Gen $ Maybe (x : a ** b x)
plus g _ = g <&> \x => tryBuild x <&> \y => (x ** y)

export
forAllDefault : Show a => Lazy a -> Gen (Maybe a) -> PropertyT a
forAllDefault def g = fromMaybe def <$> forAll g
