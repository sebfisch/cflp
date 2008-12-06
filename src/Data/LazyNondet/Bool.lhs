% Lazy Non-Deterministic Bools
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% November, 2008

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
> true :: Monad m => Typed m Bool
> true = Typed (return (cons (toConstr True) []))
>
> false :: Monad m => Typed m Bool
> false = Typed (return (cons (toConstr False) []))

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Unknown`.

> instance Unknown Bool
>  where
>   unknown = oneOf [false,true]

Some functions on `Bool`s:

> not :: (MonadConstr Choice (t cs m), RunConstr cs m t)
>     => Typed (t cs m) Bool -> cs -> Typed (t cs m) Bool
> not x = 
>   caseOf x $ \x' _ ->
>   case x' of
>     Cons _ 1 _ -> true
>     Cons _ 2 _ -> false
