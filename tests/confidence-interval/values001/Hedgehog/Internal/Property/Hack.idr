module Hedgehog.Internal.Property.Hack

import Hedgehog.Internal.Property
import public Hedgehog.Internal.Util

%default total

-- we simply export a non-exported function pretending we are friends ^_^
export
wilsonBounds' : (positives, count : Nat) -> (acceptance : InUnit) -> (Double, Double)
wilsonBounds' = wilsonBounds
