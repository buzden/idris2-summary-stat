module Data.Double.Bounded

import public Data.So

%default total

--- Auxiliary functions ---

public export %inline
OR : Type -> Type -> Type
OR = Either

infixr 0 `OR`

namespace DoubleUtils

  public export %inline
  MaxDouble, MinDouble, PosInf, NegInf : Double
  MaxDouble = 1.79769e+308
  MinDouble = -MaxDouble
  PosInf = 1/0
  NegInf = -1/0

  public export %inline
  min4 : Double -> Double -> Double -> Double -> Double
  min4 a b c d = a `min` (b `min` (c `min` d))

  public export %inline
  min6 : Double -> Double -> Double -> Double -> Double -> Double -> Double
  min6 a b c d e f = a `min` (b `min` min4 c d e f)

  public export %inline
  max4 : Double -> Double -> Double -> Double -> Double
  max4 a b c d = a `max` (b `max` (c `max` d))

  public export %inline
  max6 : Double -> Double -> Double -> Double -> Double -> Double -> Double
  max6 a b c d e f = a `max` (b `max` max4 c d e f)

  -- Returns zero if `l <= 0 <= u`, or `l` or `u` otherwise
  public export
  zormin : (l, u : Double) -> Double
  zormin l u = max l (0 `min` u)

  public export %inline
  Finite : Double -> Type
  Finite x = So (x /= NegInf && x /= PosInf)

  public export %inline
  NonZero : Double -> Type
  NonZero x = So (x /= 0)

namespace DoubleProperties

  export
  lteRefl : {0 x : Double} -> (0 _ : So $ x == x) => So $ x <= x
  lteRefl = believe_me Oh

  export
  lteNotNaNL : {0 x, y : Double} -> (0 _ : So $ x <= y) => So $ x == x
  lteNotNaNL = believe_me Oh

  export
  lteNotNaNR : {0 x, y : Double} -> (0 _ : So $ y <= x) => So $ x == x
  lteNotNaNR = believe_me Oh

  export
  lteTrans : {0 a, b, c : Double} -> (0 _ : So $ a <= b) => (0 _ : So $ b <= c) => So $ a <= c
  lteTrans = believe_me Oh

  export
  lteNegInf : {0 x : Double} -> (0 _ : So $ x == x) => So $ NegInf <= x
  lteNegInf = believe_me Oh

  export
  ltePosInf : {0 x : Double} -> (0 _ : So $ x == x) => So $ x <= PosInf
  ltePosInf = believe_me Oh

  export
  lteMin : {0 x : Double} -> (0 _ : So $ x == x) => (0 _ : Finite x) => So $ MinDouble <= x
  lteMin = believe_me Oh

  export
  lteMax : {0 x : Double} -> (0 _ : So $ x == x) => (0 _ : Finite x) => So $ x <= MaxDouble
  lteMax = believe_me Oh

  export
  lteFromLt : {0 x, y : Double} -> (0 _ : So $ x < y) => So $ x <= y
  lteFromLt = believe_me Oh

  export
  lteRev : {0 x, y : Double} -> (0 _ : So $ x == x) => (0 _ : So $ y == y) => (0 _ : So $ not $ x <= y) => So $ y < x
  lteRev = believe_me Oh

--- Type definitions ---

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
SolidDouble = DoubleBetween NegInf PosInf

public export %inline
FiniteDouble : Type
FiniteDouble = DoubleBetween MinDouble MaxDouble

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

public export %inline
relaxToSolid : DoubleBetween l u -> SolidDouble
relaxToSolid x@(BoundedDouble _ @{lb} @{rb}) = weakenBounds x @{lteNegInf @{lteNotNaNL @{lb}}} @{ltePosInf @{lteNotNaNR @{rb}}}

public export %inline
relaxToFinite : (0 _ : Finite l) => (0 _ : Finite u) => DoubleBetween l u -> FiniteDouble
relaxToFinite x@(BoundedDouble _ @{lb} @{rb}) = weakenBounds x @{lteMin @{lteNotNaNL @{lb}}} @{lteMax @{lteNotNaNR @{rb}}}

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
  (/=) = (/=) `on` (.asDouble)

public export
Ord (DoubleBetween l u) where
  compare = compare `on` (.asDouble)
  (<)  = (<)  `on` (.asDouble)
  (<=) = (<=) `on` (.asDouble)
  (>)  = (>)  `on` (.asDouble)
  (>=) = (>=) `on` (.asDouble)

--- Printing ---

public export
Show (DoubleBetween l u) where
  show $ BoundedDouble x = show x

--- Important constants ---

public export %inline
NegInf : (0 _ : So $ u == u) => DoubleBetween NegInf u
NegInf = BoundedDouble NegInf @{%search} @{lteNegInf}

public export %inline
PosInf : (0 _ : So $ l == l) => DoubleBetween l PosInf
PosInf = BoundedDouble PosInf @{ltePosInf}

public export %inline
pi, Pi : DoubleBetween Prelude.pi Prelude.pi
pi = MinimalBounds.fromDouble pi
Pi = pi

public export %inline
euler, Euler : DoubleBetween Prelude.euler Prelude.euler
euler = MinimalBounds.fromDouble euler
Euler = euler

--- Analysis operations ---

export
bisect : (m : DoubleBetween l u) -> DoubleBetween l u -> DoubleBetween l m.asDouble `OR` DoubleBetween m.asDouble u
bisect (BoundedDouble m @{lm}) (BoundedDouble x @{lb}) with (x <= m) proof xm
  _ | True  = Left $ BoundedDouble x @{%search} @{eqToSo xm}
  _ | False = Right $ BoundedDouble x @{do
                let smx = eqToSo $ cong not xm
                let xx = lteNotNaNR @{lb}
                let mm = lteNotNaNR @{lm}
                lteFromLt @{lteRev}
              }

--- Basic arithmetics ---

export
(+) : DoubleBetween l u ->
      DoubleBetween l' u' ->
      (0 _ : Finite l `OR` Finite l' `OR` So (l == l')) =>
      (0 _ : Finite u `OR` Finite u' `OR` So (u == u')) =>
      DoubleBetween (l+l') (u+u')
BoundedDouble x + BoundedDouble y = BoundedDouble (x + y) @{believe_me Oh} @{believe_me Oh}

export
(-) : DoubleBetween l u ->
      DoubleBetween l' u' ->
      (0 _ : Finite l `OR` Finite u' `OR` So (l /= u')) =>
      (0 _ : Finite u `OR` Finite l' `OR` So (u /= l')) =>
      DoubleBetween (l-u') (u-l')
BoundedDouble x - BoundedDouble y = BoundedDouble (x - y) @{believe_me Oh} @{believe_me Oh}

export
(*) : DoubleBetween l u ->
      DoubleBetween l' u' ->
      (0 _ : Finite l `OR` NonZero l') =>
      (0 _ : Finite l `OR` NonZero u') =>
      (0 _ : Finite u `OR` NonZero l') =>
      (0 _ : Finite u `OR` NonZero u') =>
      (0 _ : Finite l' `OR` NonZero l) =>
      (0 _ : Finite l' `OR` NonZero u) =>
      (0 _ : Finite u' `OR` NonZero l) =>
      (0 _ : Finite u' `OR` NonZero u) =>
      DoubleBetween (min4 (l*l') (l*u') (u*l') (u*u')) (max4 (l*l') (l*u') (u*l') (u*u'))
BoundedDouble x * BoundedDouble y = BoundedDouble (x * y) @{believe_me Oh} @{believe_me Oh}

export
(/) : {l, u, l', u' : _} ->
      (num : DoubleBetween l u) ->
      (den : DoubleBetween l' u') ->
      (0 _ : So (0 < l') `OR` So (u' < 0) `OR` So (l' < 0 && 0 < u' && l /= 0 && u /= 0)) =>
      (0 _ : So (0 < l) `OR` So (u < 0) `OR` So (0 < l') `OR` So (u' < 0) `OR` (NonZero num.asDouble, NonZero den.asDouble)) =>
      (0 _ : Finite l `OR` Finite l') =>
      (0 _ : Finite l `OR` Finite u') =>
      (0 _ : Finite u `OR` Finite l') =>
      (0 _ : Finite u `OR` Finite u') =>
      (0 _ : NonZero l `OR` NonZero l') =>
      (0 _ : NonZero l `OR` NonZero u') =>
      (0 _ : NonZero u `OR` NonZero l') =>
      (0 _ : NonZero u `OR` NonZero u') =>
      DoubleBetween
        (min6 (l/l') (l/u') (u/l') (u/u') (l/zormin l' u') (u/zormin l' u'))
        (max6 (l/l') (l/u') (u/l') (u/u') (l/zormin l' u') (u/zormin l' u'))
BoundedDouble x / BoundedDouble y = fit (x / y) where
  fit : {ll, uu : Double} -> (x : Double) -> DoubleBetween ll uu
  fit x = do
    let x = if x < ll then ll else if uu < x then uu else x
    BoundedDouble x @{believe_me Oh} @{believe_me Oh}

export
negate : DoubleBetween l u -> DoubleBetween (-u) (-l)
negate x = BoundedDouble (negate x.asDouble) @{believe_me Oh} @{believe_me Oh}

--- Math functions ---

export
sqrt : (0 _ : So $ 0 <= l) => DoubleBetween l u -> DoubleBetween (sqrt l) (sqrt u)
sqrt x = BoundedDouble (sqrt x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
sqrtRelaxed : (0 _ : So $ 0 <= l) => DoubleBetween l u -> DoubleBetween 0 PosInf
sqrtRelaxed x = BoundedDouble (sqrt x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
log : (0 _ : So $ 0 <= l) => DoubleBetween l u -> DoubleBetween (log l) (log u)
log x = BoundedDouble (log x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
exp : DoubleBetween l u -> DoubleBetween (exp l) (exp u)
exp x = BoundedDouble (exp x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
expRelaxed : DoubleBetween l u -> DoubleBetween 0 PosInf
expRelaxed x = BoundedDouble (exp x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
sin : FiniteDouble -> DoubleBetween (-1) 1
sin x = BoundedDouble (sin x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
cos : FiniteDouble -> DoubleBetween (-1) 1
cos x = BoundedDouble (cos x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
asin : DoubleBetween (-1) 1 -> DoubleBetween (-Prelude.pi/2) (Prelude.pi/2)
asin x = BoundedDouble (asin x.asDouble) @{believe_me Oh} @{believe_me Oh}

export
acos : DoubleBetween (-1) 1 -> DoubleBetween 0 Prelude.pi
acos x = BoundedDouble (acos x.asDouble) @{believe_me Oh} @{believe_me Oh}
