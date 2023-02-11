module Test.Common

import Hedgehog

import Statistics.Probability

import public Test.Hedgehog.BoundedDoubles

%default total

namespace Probability

  export
  eqUpToEps : Eps => Probability -> Probability -> Bool
  eqUpToEps = eqUpToEps `on` (.asDouble)

export
probabilityCorrect : Probability -> PropertyT ()
probabilityCorrect p = boundedDoubleCorrect p.value

export
anyProbability : Gen Probability
anyProbability = P <$> anyBoundedDouble _ _

--- Special common properties ---

namespace ToProbability

  export
  un_corr : {l, u : _} -> (0 _ : So $ l <= u) => (DoubleBetween l u -> Probability) -> Property
  un_corr f = un_corr $ (.value) . f

namespace FromProbability

  export
  un_corr : {l', u' : _} -> (Probability -> DoubleBetween l' u') -> Property
  un_corr f = un_corr $ f . P
