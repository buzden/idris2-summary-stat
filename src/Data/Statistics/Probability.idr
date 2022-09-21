module Data.Statistics.Probability

import public Data.So

%default total

--- Data definition ---

public export
inProbBounds : Double -> Bool
inProbBounds x = 0 <= x && x <= 1

public export
data Probability : Type where
  P : (x : Double) -> (0 _ : So $ inProbBounds x) => Probability

--- Literals syntax ---

public export %inline
fromDouble : (x : Double) -> (0 _ : So $ inProbBounds x) => Probability
fromDouble = P

public export %inline
fromInteger : (n : Integer) -> (0 _ : Either (n = 0) (n = 1)) => Probability
fromInteger n = P (cast n) @{believe_me Oh}

--- Conversions ---

public export
Cast Probability Double where
  cast $ P x = x

public export %inline
(.asDouble) : Probability -> Double
(.asDouble) = cast

public export
maybeP : Double -> Maybe Probability
maybeP x with (inProbBounds x) proof p
  _ | True  = Just $ P x @{eqToSo p}
  _ | False = Nothing

namespace FromDoubles

  export
  (/) : (num, den : Double) -> (0 _ : So $ 1 < num && num <= den) => Probability
  num / den = P (num / den) @{believe_me Oh}

export
(.percent) : (x : Double) -> (0 _ : So $ 0 <= x && x <= 100) => Probability
x.percent = (x / 100) @{believe_me Oh}

--- Composition operations ---

export
(*) : Probability -> Probability -> Probability
P x * P y = P (x * y) @{believe_me Oh}

public export
Semigroup Probability where
  (<+>) = (*)

public export
Monoid Probability where
  neutral = P 1

export
(/) : Probability -> (y : Double) -> (0 _ : So $ y >= 1) => Probability
P x / y = P (x / y) @{believe_me Oh}

export
inv : Probability -> Probability
inv $ P x = P (1 - x) @{believe_me Oh}

public export %inline
(.inv) : Probability -> Probability
(.inv) = inv

--- Comparison operations ---

public export
Eq Probability where
  P x == P y = x == y

public export
Ord Probability where
  compare (P x) (P y) = compare x y
