% Lazy Non-Deterministic Bools
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic booleans.

> module Data.LazyNondet.Bool where
>
> import Data.Data
> import Data.LazyNondet
>
> import Control.Monad.Constraint
>
> instance DataConstr Bool where dataConstr = toConstr
>
> true :: Monad m => Nondet m Bool
> true = cons True
>
> pTrue :: (cs -> Nondet m a) -> (ConIndex, cs -> Branch m a)
> pTrue = branch True
>
> false :: Monad m => Nondet m Bool
> false = cons False
>
> pFalse :: (cs -> Nondet m a) -> (ConIndex, cs -> Branch m a)
> pFalse = branch False

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Unknown`.

> instance Unknown Bool
>  where
>   unknown = oneOf [false,true]

Some operations on `Bool`s:

> not :: MonadSolve cs m m => Nondet m Bool -> cs -> Nondet m Bool
> not x = caseOf_ x [pFalse (\_ -> true)] false

