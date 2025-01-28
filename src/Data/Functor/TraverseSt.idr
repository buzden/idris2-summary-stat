module Data.Functor.TraverseSt

import Control.Monad.State

import Data.Colist
import Data.List.Lazy

%default total

-----------------
--- Interface ---
-----------------

-- A particular case of sub-traversability with the state monad.
-- This is not a full traverse because state is not returned,
-- thus there is no way to demand the final state.
-- This allows us to implement this interface for (potentially) infinite data types.
public export
interface TraversableSt f where
  traverseSt : s -> (a -> s -> (s, b)) -> f a -> f b

--------------------------------------
--- Particular universal functions ---
--------------------------------------

export %inline
withIndex : TraversableSt f => f a -> f (Nat, a)
withIndex = traverseSt Z $ \x, n => (S n, n, x)

export %inline
(.withIndex) : TraversableSt f => f a -> f (Nat, a)
(.withIndex) = withIndex

------------------------------------------
--- Implementations for standard types ---
------------------------------------------

public export
TraversableSt Stream where
  traverseSt s f (x::xs) = do
    let (s', y) = f x s
    y :: traverseSt s' f xs

public export
TraversableSt Colist where
  traverseSt _ _ []      = []
  traverseSt s f (x::xs) = do
    let (s', y) = f x s
    y :: traverseSt s' f xs

public export
TraversableSt LazyList where
  traverseSt _ _ []      = []
  traverseSt s f (x::xs) = do
    let (s', y) = f x s
    y :: traverseSt s' f xs

public export
Traversable f => TraversableSt f where
  traverseSt s f = evalState s . traverse (ST . pure .: f)

------------------------------------------------------
--- Additional implementations of other interfaces ---
------------------------------------------------------

namespace Functor

  public export
  [FromTraversableSt] TraversableSt f => Functor f where
    map f = traverseSt () $ const . pure . f
