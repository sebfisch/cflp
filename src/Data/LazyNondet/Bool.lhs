% Lazy Non-Deterministic Bools
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic booleans.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.Bool where
>
> import Data.Data
> import Data.LazyNondet
>
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> true :: Monad m => Nondet m Bool
> true = Nondet (return (mkHNF (toConstr True) []))
>
> false :: Monad m => Nondet m Bool
> false = Nondet (return (mkHNF (toConstr False) []))

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Unknown`.

> instance Unknown Bool
>  where
>   unknown = oneOf [false,true]

Some functions on `Bool`s:

> not :: MonadSolve cs m m => Nondet m Bool -> cs -> Nondet m Bool
> not x = 
>   caseOf x $ \x' _ ->
>   case x' of
>     Cons _ 1 _ -> true
>     Cons _ 2 _ -> false
