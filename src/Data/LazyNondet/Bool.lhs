% Lazy Non-Deterministic Bools
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic booleans.

> module Data.LazyNondet.Bool where
>
> import Data.Data
> import Data.LazyNondet
>
> import Control.Monad.State
> import Control.Monad.Constraint
>
> instance ConsRep Bool where consRep = toConstr
>
> true :: Monad m => Nondet m Bool
> true = cons True
>
> pTrue :: (cs -> Nondet m a) -> Match cs m a
> pTrue = match True
>
> false :: Monad m => Nondet m Bool
> false = cons False
>
> pFalse :: (cs -> Nondet m a) -> Match cs m a
> pFalse = match False

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Unknown`.

> instance Unknown Bool
>  where
>   unknown = oneOf [false,true]

Some operations with `Bool`s:

> not :: MonadSolve cs m m => Nondet m Bool -> cs -> Nondet m Bool
> not x = caseOf_ x [pFalse (\_ -> true)] false

> (===) :: MonadSolve cs m m => Nondet m a -> Nondet m a -> cs -> Nondet m Bool
> (x === y) cs = Typed $ do
>   eq <- evalStateT (prim_eq (untyped x) (untyped y)) cs
>   untyped $ if eq then true else false
