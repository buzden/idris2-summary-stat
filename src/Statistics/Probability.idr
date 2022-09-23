module Statistics.Probability

import public Data.Double.Bounded

import Data.Nat

%default total

--- Data definition ---

public export
data Probability : Type where
  P : DoubleBetween 0 1 -> Probability

--- Literals syntax ---

public export %inline
fromDouble : (x : Double) -> (0 _ : So $ 0 <= x && x <= 1) => Probability
fromDouble x @{bds} = P $ fromDouble x @{fst $ soAnd bds} @{snd $ soAnd bds}

public export %inline
fromInteger : (n : Integer) -> (0 _ : Either (n = 0) (n = 1)) => Probability
fromInteger n = fromDouble (cast n) @{believe_me Oh}

--- Conversions ---

public export %inline
Cast Probability Double where
  cast $ P x = x.asDouble

public export %inline
Cast Probability (DoubleBetween 0 1) where
  cast $ P x = x

public export %inline
Cast (DoubleBetween 0 1) Probability where
  cast = P

public export %inline
(.asDouble) : Probability -> Double
(.asDouble) = cast

public export %inline
(.asBoundedDouble) : Probability -> DoubleBetween 0 1
(.asBoundedDouble) = cast

public export
maybeP : Double -> Maybe Probability
maybeP = map P . maybeBoundedDouble

namespace FromDoubles

  export
  (/) : (num, den : Double) -> (0 _ : So $ 1 < num && num <= den) => Probability
  num / den = fromDouble (num / den) @{believe_me Oh}

export
ratio : (num, den : Nat) -> (0 _ : num `LTE` den) => (0 _ : IsSucc den) => Probability
ratio num den = (cast num / cast den) @{believe_me Oh}

public export
(.percent) : DoubleBetween 0 100 -> Probability
x.percent = P $ x / 100

--- Composition operations ---

public export
(*) : Probability -> Probability -> Probability
P x * P y = P $ x * y

public export
Semigroup Probability where
  (<+>) = (*)

public export
Monoid Probability where
  neutral = P 1

public export
(/) : Probability -> DoubleBetween 1 (1/0) -> Probability
P x / y = P $ x / y

public export %inline
inv : Probability -> Probability
inv $ P x = P $ 1 - x

public export %inline
(.inv) : Probability -> Probability
(.inv) = inv

--- Comparison operations ---

public export %inline
Eq Probability where
  P x == P y = x == y

public export %inline
Ord Probability where
  compare (P x) (P y) = compare x y

--- Printing ---

export
Show Probability where
  show $ P x = show x
