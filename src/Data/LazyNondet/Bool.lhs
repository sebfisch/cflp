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
>
> true :: Monad m => Nondet m Bool
> true = Typed (return (mkHNF (toConstr True) []))
>
> pTrue :: (cs -> Nondet m a) -> (ConIndex, cs -> Branch m a)
> pTrue alt = (constrIndex (toConstr True), Branch . alt)
>
> false :: Monad m => Nondet m Bool
> false = Typed (return (mkHNF (toConstr False) []))
>
> pFalse :: (cs -> Nondet m a) -> (ConIndex, cs -> Branch m a)
> pFalse alt = (constrIndex (toConstr False), Branch . alt)

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Unknown`.

> instance Unknown Bool
>  where
>   unknown = oneOf [false,true]

Some operations on `Bool`s:

> not :: MonadSolve cs m m => Nondet m Bool -> cs -> Nondet m Bool
> not x = caseOf_ x [pFalse (\_ -> true)] false

