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

Instances for the classes `ApplyCons` and `Generic` for booleans are
defined in the module `Data.LazyNondet.Generic`.

> false, true :: Monad m => Nondet c m Bool
> false :! true :! () = constructors
>
> pFalse, pTrue :: (Context c -> Nondet c m a) -> Match Bool c m a
> pFalse :! pTrue :! () = patterns

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Narrow`.

> instance Narrow Bool
>  where
>   narrow = oneOf [false,true]

Some operations with `Bool`s:

> not :: (MonadPlus m, Update c m m)
>     => Nondet c m Bool -> Context c -> Nondet c m Bool
> not x = caseOf_ x [pFalse (const true)] false
>
> (===) :: (Monad m, Update c m m)
>       => Nondet c m a -> Nondet c m a -> Context c -> Nondet c m Bool
> (x === y) (Context cs) = Typed $ do
>   eq <- evalStateT (prim_eq (untyped x) (untyped y)) cs
>   untyped $ if eq then true else false
