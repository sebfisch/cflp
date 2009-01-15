% Lazy Non-Deterministic Bools
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic booleans.

> {-# LANGUAGE
>       NoMonomorphismRestriction,
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       NoMonoPatBinds
>   #-}
>
> module Data.LazyNondet.Types.Bool where
>
> import Data.LazyNondet
> import Data.LazyNondet.Types
> import Data.LazyNondet.Primitive
>
> import Control.Monad.State
> import Control.Monad.Update
>
> import Control.Constraint.Choice

Instances for the classes `ApplyCons` and `Generic` for booleans are
defined in the module `Data.LazyNondet.Generic`.

> false, true :: Monad m => Nondet cs m Bool
> false :! true :! () = constructors
>
> pFalse, pTrue :: (Context cs -> Nondet cs m a) -> Match Bool cs m a
> pFalse :! pTrue :! () = patterns

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Narrow`.

> instance ChoiceStore cs => Narrow cs Bool
>  where
>   narrow = oneOf [false,true]

Some operations with `Bool`s:

> not :: Update cs m m => Nondet cs m Bool -> Context cs -> Nondet cs m Bool
> not x = caseOf_ x [pFalse (const true)] false
>
> (===) :: Update cs m m
>       => Nondet cs m a -> Nondet cs m a -> Context cs -> Nondet cs m Bool
> (x === y) (Context cs) = Typed $ do
>   eq <- evalStateT (prim_eq (untyped x) (untyped y)) cs
>   untyped $ if eq then true else false
