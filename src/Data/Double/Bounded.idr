module Data.Double.Bounded

import public Data.So

%default total

namespace DoubleProperties

  export
  lteRefl : {0 x : Double} -> (0 _ : So $ x == x) => So $ x <= x
  lteRefl = believe_me Oh

  export
  lteTrans : {0 a, b, c : Double} -> (0 _ : So $ a <= b) => (0 _ : So $ b <= c) => So $ a <= c
  lteTrans = believe_me Oh

||| The type of double in the given bounds.
|||
||| Both bounds and the value can be infinite.
||| If either bounds is `NaN`, the type is uninhabited.
||| The internal double value cannot be `NaN` since to inhabit the constructor,
||| one needs to satisfy the bounds which is impossible with `NaN` value.
public export
data DoubleBetween : (lower, upper : Double) -> Type where
  BoundedDouble :
    {0 lower, upper : Double} ->
    (x : Double) ->
    (0 _ : So $ lower <= x) =>
    (0 _ : So $ x <= upper) =>
    DoubleBetween lower upper

||| Represents a bounded double which can hold any `Double` except the `NaN`.
||| Actually, an alias for `DoubleBetween` with infinite bounds.
public export %inline
SolidDouble : Type
SolidDouble = DoubleBetween (-1.0/0) (1.0/0)

--- Conversions ---

public export
maybeBoundedDouble : {lower, upper : Double} -> (x : Double) -> Maybe $ DoubleBetween lower upper
maybeBoundedDouble x with (lower <= x) proof lx
  _ | False = Nothing
  _ | True with (x <= upper) proof xu
    _ | False = Nothing
    _ | True  = Just $ BoundedDouble x @{eqToSo lx} @{eqToSo xu}

public export
Cast (DoubleBetween l u) Double where
  cast $ BoundedDouble x = x

public export %inline
(.asDouble) : DoubleBetween l u -> Double
(.asDouble) = cast

public export
weakenBounds : DoubleBetween l u -> (0 _ : So $ l' <= l) => (0 _ : So $ u <= u') => DoubleBetween l' u'
weakenBounds $ BoundedDouble x = BoundedDouble x @{lteTrans {b=l}} @{lteTrans {b=u}}

public export
strengthenBounds : {l', u' : _} -> DoubleBetween l u -> Maybe $ DoubleBetween l' u'
strengthenBounds = maybeBoundedDouble . cast

--- Literals syntax ---

namespace MinimalBounds

  public export %inline
  fromDouble : (x : Double) -> (0 _ : So $ x == x) => DoubleBetween x x
  fromDouble x = BoundedDouble x @{lteRefl} @{lteRefl}

  public export %inline
  fromInteger : (x : Integer) -> (0 _ : So $ cast {to=Double} x == cast x) => DoubleBetween (cast x) (cast x)
  fromInteger x = BoundedDouble (cast x) @{lteRefl} @{lteRefl}

namespace KnownBounds

  public export %inline
  fromDouble : (x : Double) -> (0 _ : So $ lower <= x) => (0 _ : So $ x <= upper) => DoubleBetween lower upper
  fromDouble x = BoundedDouble x

  public export %inline
  fromInteger : (x : Integer) -> (0 _ : So $ lower <= cast x) => (0 _ : So $ cast x <= upper) => DoubleBetween lower upper
  fromInteger x = BoundedDouble $ cast x

--- Comparison ---

public export
Eq (DoubleBetween l u) where
  (==) = (==) `on` (.asDouble)

public export
Ord (DoubleBetween l u) where
  compare = compare `on` (.asDouble)

--- Printing ---

public export
Show (DoubleBetween l u) where
  show $ BoundedDouble x = show x

--- Auxiliary functions ---

public export %inline
min4 : Double -> Double -> Double -> Double -> Double
min4 a b c d = a `min` (b `min` (c `min` d))

public export %inline
max4 : Double -> Double -> Double -> Double -> Double
max4 a b c d = a `max` (b `max` (c `max` d))

public export %inline
OR : Type -> Type -> Type
OR = Either

infixr 0 `OR`

--- Basic arithmetics ---

export
(+) : DoubleBetween l u -> DoubleBetween l' u' -> DoubleBetween (l+l') (u+u')
BoundedDouble x + BoundedDouble y = BoundedDouble (x + y) @{believe_me Oh} @{believe_me Oh}

export
(-) : DoubleBetween l u -> DoubleBetween l' u' -> DoubleBetween (l-u') (u-l')
BoundedDouble x - BoundedDouble y = BoundedDouble (x - y) @{believe_me Oh} @{believe_me Oh}

export
(*) : DoubleBetween l u -> DoubleBetween l' u' -> DoubleBetween (min4 (l*l') (l*u') (u*l') (u*u')) (max4 (l*l') (l*u') (u*l') (u*u'))
BoundedDouble x * BoundedDouble y = BoundedDouble (x * y) @{believe_me Oh} @{believe_me Oh}

-- TODO this signature works badly when at least two of four bounds are infinite, NaN appears.
export
(/) : {l, u, l', u' : _} ->
      (num : DoubleBetween l u) ->
      (den : DoubleBetween l' u') ->
      (0 _ : So (0 < l') `OR` So (u' < 0) `OR` So (l' < 0 && 0 < u' && den.asDouble /= 0)) =>
      DoubleBetween (min4 (l/l') (l/u') (u/l') (u/u')) (max4 (l/l') (l/u') (u/l') (u/u'))
BoundedDouble x / BoundedDouble y = fit (x / y) where
  fit : {ll, uu : Double} -> (x : Double) -> DoubleBetween ll uu
  fit x = do
    let x = if x < ll then ll else if uu < x then uu else x
    BoundedDouble x @{believe_me Oh} @{believe_me Oh}
