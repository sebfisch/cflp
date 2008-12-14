% Lazy Non-Deterministic Bools
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic booleans.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.Types.Bool where
>
> import Data.Data
> import Data.LazyNondet
> import Data.LazyNondet.Types
> import Data.LazyNondet.Primitive
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> instance ConsRep Bool where consRep = toConstr
>
> true :: Monad m => Nondet cs m Bool
> true = cons True
>
> pTrue :: (cs -> Nondet cs m a) -> Match Bool cs m a
> pTrue = match True
>
> false :: Monad m => Nondet cs m Bool
> false = cons False
>
> pFalse :: (cs -> Nondet cs m a) -> Match Bool cs m a
> pFalse = match False

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Narrow`.

> instance ChoiceStore cs => Narrow cs Bool
>  where
>   narrow = oneOf [false,true]

Some operations with `Bool`s:

> not :: (MonadSolve cs m m, MonadConstr Choice m)
>     => Nondet cs m Bool -> cs -> Nondet cs m Bool
> not x = caseOf_ x [pFalse (\_ -> true)] false
>
> (===) :: MonadSolve cs m m
>       => Nondet cs m a -> Nondet cs m a -> cs -> Nondet cs m Bool
> (x === y) cs = Typed $ do
>   eq <- evalStateT (prim_eq (untyped x) (untyped y)) cs
>   untyped $ if eq then true else false
