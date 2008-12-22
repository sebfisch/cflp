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
> import Data.Maybe
> import Data.LazyNondet.Types
>
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> import Data.Supply
>
> unknown :: (MonadConstr Choice m, Narrow cs a) => ID -> Nondet cs m a
> unknown u = freeVar u (delayed (redelay u) (\cs -> narrow cs u))
>
> redelay :: ChoiceStore cs => ID -> cs -> Bool
> redelay (ID us) = isNothing . lookupChoice (supplyValue us)

The application of `unknown` to a constraint store and a unique
identifier represents a logic variable of an arbitrary type. 

> class ChoiceStore cs => Narrow cs a
>  where
>   narrow :: MonadConstr Choice m => cs -> ID -> Nondet cs m a

Logic variables of type `a` can be narrowed to head-normal form if
there is an instance of the type class `Narrow`. A constraint store
may be used to find the possible results which are returned in a monad
that supports choices. Usually, `narrow` will be implemented as a
non-deterministic generator using `oneOf`, but for specific types
different strategies may be implemented.

> (?) :: (MonadConstr Choice m, ChoiceStore cs)
>     => Nondet cs m a -> Nondet cs m a -> ID -> Nondet cs m a
> (x ? y) u = delayed (redelay u) (\cs -> oneOf [x,y] cs u)

The operator `(?)` wraps the combinator `oneOf` to generate a delayed
non-deterministic choice that is executed whenever it is
demanded. Although the choice itself is reexecuted according to the
current constraint store, the arguments of `(?)` are shared among all
executions and *not* reexecuted.

> oneOf :: (MonadConstr Choice m, ChoiceStore cs)
>       => [Nondet cs m a] -> cs -> ID -> Nondet cs m a
> oneOf xs cs (ID us) = Typed (choice cs (supplyValue us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.
