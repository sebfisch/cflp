% Combinators for Programs on Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       FlexibleContexts,
>       FlexibleInstances,
>       MultiParamTypeClasses,
>       FunctionalDependencies
>   #-}
>
> module Data.LazyNondet.Combinators (
>
>   cons, failure, oneOf, ConsRep(..)
>
> ) where
>
> import Data.Data
> import Data.LazyNondet.Types
>
> import Control.Monad
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> import UniqSupply
>
> oneOf :: (MonadConstr Choice m, ChoiceStore cs)
>       => [Nondet cs m a] -> cs -> ID -> Nondet cs m a
> oneOf xs cs (ID us) = Typed (choice cs (uniqFromSupply us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.

> failure :: MonadPlus m => Nondet cs m a
> failure = Typed mzero

A failing computation could be defined using `oneOf`, but we provide a
special combinator that does not need a supply of unique identifiers.

> class MkCons cs m a b | b -> m, b -> cs
>  where
>   mkCons :: a -> [Untyped cs m] -> b
>
> instance (Monad m, Data a) => MkCons cs m a (Nondet cs m t)
>  where
>   mkCons c args = Typed (return (mkHNF (toConstr c) (reverse args)))
>
> instance MkCons cs m b c => MkCons cs m (a -> b) (Nondet cs m t -> c)
>  where
>   mkCons c xs x = mkCons (c undefined) (untyped x:xs)
>
> cons :: MkCons cs m a b => a -> b
> cons c = mkCons c []

The overloaded operation `cons` takes a Haskell constructor and yields
a corresponding constructor function for non-deterministic values.

> class ConsRep a
>  where
>   consRep :: a -> Constr
>
> instance ConsRep b => ConsRep (a -> b)
>  where
>   consRep c = consRep (c undefined)

We provide an overloaded operation `consRep` that yields a `Constr`
representation for a constructor rather than for a constructed value
like `Data.Data.toConstr` does. We do not provide the base instance

    instance Data a => ConsRep a
     where
      consRep = toConstr

because this would require to allow undecidable instances. As a
consequence, specialized base instances need to be defined for every
used datatype. See `Data.LazyNondet.List` for an example of how to get
the representation of polymorphic constructors and destructors.
