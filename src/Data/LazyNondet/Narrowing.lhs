% Logic Variables and Narrowing
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       FlexibleContexts,
>       MultiParamTypeClasses
>   #-}
>
> module Data.LazyNondet.Narrowing (
>
>   unknown, Narrow(..), NarrowPolicy(..)
>
> ) where
>
> import Data.LazyNondet.Types
>
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> unknown :: (MonadConstr Choice m, Narrow cs a) => cs -> ID -> Nondet cs m a
> unknown cs u = freeVar u (narrowWithPolicy cs u)

The application of `unknown` to a constraint store and a unique
identifier represents a logic variable of an arbitrary type. 

> class ChoiceStore cs => Narrow cs a
>  where
>   narrowPolicy :: NarrowPolicy cs a
>   narrowPolicy = OnDemand
>
>   narrow :: MonadConstr Choice m => cs -> ID -> Nondet cs m a

Logic variables of type `a` can be narrowed to head-normal form if
there is an instance of the type class `Narrow`. A constraint store
may be used to find the possible results which are returned in a monad
that supports choices. Usually, `narrow` will be implemented as a
non-deterministic generator using `oneOf`, but for specific types
different strategies may be implemented.

The default policy is to narrow on demand in order to avoid
unnessesary choices in shared free variables that can lead to
exponential explosion of the search space.

A `NarrowPolicy` specifies whether a logic variable should be

 * narrowed whenever it is demanded according the current constraint
   store or

 * narrowed only on creation and shared on every demand.

> data NarrowPolicy cs a = OnDemand | OnCreation

Using `OnDemand` can avoid unnessesary branching when accessing a
variable with an updated constraint store. Using `OnCreation` will
avoid the reexecution of a non-deterministic generator.

> narrowWithPolicy :: (MonadConstr Choice m, Narrow cs a)
>                  => cs -> ID -> Nondet cs m a
> narrowWithPolicy cs u = x
>  where
>   x = case policy x of
>         OnDemand   -> execute (`narrow`u)
>         OnCreation -> narrow cs u
>
> policy :: Narrow cs a => Nondet cs m a -> NarrowPolicy cs a
> policy _ = narrowPolicy

The function `narrowWithPolicy` narrows a logic variable or creates a
delayed execution that will be performed whenever the variable is
demanded. The definition uses a helper function in order to constrain
the type of the narrowing policy.
