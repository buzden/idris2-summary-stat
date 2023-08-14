module Data.Functor.TraverseSt

import Control.Monad.State

import Data.Colist
import Data.List.Lazy

%default total

-- A particular case of sub-traversability with the state monad.
-- This is not a full traverse because state is not returned,
-- thus there is no way to demand the final state.
-- This allows us to implement this interface for (potentially) infinite data types.
public export
interface TraversableSt f where
  mapSt : (a -> s -> (s, b)) -> s -> f a -> f b

public export
TraversableSt Stream where
  mapSt f s (x::xs) = do
    let (s', y) = f x s
    y :: mapSt f s' xs

public export
TraversableSt Colist where
  mapSt _ _ []      = []
  mapSt f s (x::xs) = do
    let (s', y) = f x s
    y :: mapSt f s' xs

public export
TraversableSt LazyList where
  mapSt _ _ []      = []
  mapSt f s (x::xs) = do
    let (s', y) = f x s
    y :: mapSt f s' xs

public export
Traversable f => TraversableSt f where
  mapSt f s = evalState s . traverse (ST . pure .: f)

namespace Functor

  public export
  [FromTraversableSt] TraversableSt f => Functor f where
    map f = mapSt (const . pure . f) ()
