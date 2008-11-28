% Lazy Functional-Logic Programming
% [Sebastian Fischer](mailto:sebf@informatik.uni-kiel.de)
% November, 2008

This module provides an interface that can be used for lazy
functional-logic programming in Haskell.

~~~ { .LiterateHaskell }

> {-# OPTIONS
>      -XMultiParamTypeClasses
>      -XFlexibleContexts
>   #-}
>
> module Control.LazyFLP (
>
>   FLP,
>
>   module Data.LazyNondet,
>   module Data.LazyNondet.Bool,
>   module Data.LazyNondet.List
>
> ) where
>
> import Data.LazyNondet
> import Data.LazyNondet.Bool
> import Data.LazyNondet.List
>
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> class (MonadConstr Choice (t cs m), RunConstr cs m t) => FLP t cs m

~~~

The type class `FLP` is a shortcut for the type-class constraints on
lazy functional-logic operations.

