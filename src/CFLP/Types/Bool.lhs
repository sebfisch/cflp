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
> module CFLP.Types.Bool where
>
> import Control.Monad.State
>
> import CFLP
> import CFLP.Data.Types
> import CFLP.Data.Primitive

Instances for the classes `ApplyCons` and `Generic` for booleans are
defined in the module `CFLP.Data.Generic`.

> false, true :: Monad m => Nondet c m Bool
> false :! true :! () = constructors
>
> pFalse, pTrue :: (Context c -> Nondet c m a) -> Match Bool c m a
> pFalse :! pTrue :! () = patterns

In order to be able to use logic variables of boolean type, we make it
an instance of the type class `Narrow`.

> instance Narrow c Bool
>  where
>   narrow = oneOf [false,true]

Some operations with `Bool`s:

> not :: CFLP s
>     => Data s Bool -> Context (Ctx s) -> Data s Bool
> not x = caseOf_ x [pFalse (const true)] false
>
> (===) :: CFLP s => Data s a -> Data s a -> Context (Ctx s) -> Data s Bool
> (x === y) (Context cs) = Typed $ do
>   eq <- evalStateT (prim_eq (untyped x) (untyped y)) cs
>   untyped $ if eq then true else false
