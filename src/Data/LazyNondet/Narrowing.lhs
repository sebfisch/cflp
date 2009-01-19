% Logic Variables and Narrowing
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       FlexibleContexts,
>       MultiParamTypeClasses
>   #-}
>
> module Data.LazyNondet.Narrowing (
>
>   unknown, Narrow(..), oneOf, (?)
>
> ) where
>
> import Data.LazyNondet.Types
>
> import Control.Monad.Update
> import Control.Strategy
>
> import Data.Supply
>
> unknown :: (Monad s, Strategy c s, MonadUpdate c s, Narrow a)
>         => ID -> Nondet c s a
> unknown u = freeVar u (delayed (isNarrowedID u) (`narrow`u))
>
> isNarrowedID :: Strategy c s => ID -> Context c -> s Bool
> isNarrowedID (ID us) (Context c) = isNarrowed c (supplyValue us)

The application of `unknown` to a constraint store and a unique
identifier represents a logic variable of an arbitrary type. 

> class Narrow a
>  where
>   narrow :: (Monad s, Strategy c s, MonadUpdate c s)
>          => Context c -> ID -> Nondet c s a

Logic variables of type `a` can be narrowed to head-normal form if
there is an instance of the type class `Narrow`. A constraint store
may be used to find the possible results which are returned in a monad
that supports choices. Usually, `narrow` will be implemented as a
non-deterministic generator using `oneOf`, but for specific types
different strategies may be implemented.

> (?) :: (Monad s, Strategy c s, MonadUpdate c s)
>     => Nondet c s a -> Nondet c s a -> ID -> Nondet c s a
> (x ? y) u = delayed (isNarrowedID u) (\c -> oneOf [x,y] c u)

The operator `(?)` wraps the combinator `oneOf` to generate a delayed
non-deterministic choice that is executed whenever it is
demanded. Although the choice itself is reexecuted according to the
current constraint store, the arguments of `(?)` are shared among all
executions and *not* reexecuted.

> oneOf :: (Strategy c s, MonadUpdate c s)
>       => [Nondet c s a] -> Context c -> ID -> Nondet c s a
> oneOf xs (Context c) (ID us)
>   = Typed (choose c (supplyValue us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.
