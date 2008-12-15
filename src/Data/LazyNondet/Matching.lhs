% Pattern Matching of Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       RankNTypes,
>       TypeFamilies,
>       FlexibleContexts,
>       FlexibleInstances,
>       MultiParamTypeClasses,
>       FunctionalDependencies,
>       ExistentialQuantification
>   #-}
>
> module Data.LazyNondet.Matching (
>
>   Match, match, ConsRep(..), cons,
>
>   withHNF, failure, caseOf, caseOf_
>
> ) where
>
> import Data.Data
> import Data.LazyNondet.Types
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> withHNF :: (Monad m, MonadSolve cs m m)
>         => Nondet cs m a
>         -> (HeadNormalForm cs m -> cs -> Nondet cs m b)
>         -> cs -> Nondet cs m b
> withHNF x b cs = Typed (do
>   (hnf,cs') <- runStateT (solve (untyped x)) cs
>   untyped (b hnf cs'))

The `withHNF` operation can be used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value. An updated constraint store is passed to the computation of the
branch function. Collected constraints are kept attached to the
computed value by using an appropriate instance of `MonadSolve` that
does not eliminate them.

> class WithUntyped a
>  where
>   type C a
>   type M a :: * -> *
>   type T a
>
>   withUntyped :: a -> [Untyped (C a) (M a)] -> Nondet (C a) (M a) (T a)

We repeat the definition of the type class `With` because the current
implementation of GHC does not allow equality constraints in
super-class constraints. We would prefer to define this class as
follows:

    class (With [Untyped cs m] a, m ~ Mon [Untyped cs m] a) => WithUnique a
     where
      withUnique :: a -> [Untyped cs m] -> Nondet cs m (Typ [Untyped cs m] a)
      withUnique = with

So it is just a copy of the type class `With` where the argument type
is specialized to use the same monad.

> instance WithUntyped (Nondet cs m a)
>  where
>   type C (Nondet cs m a) = cs
>   type M (Nondet cs m a) = m
>   type T (Nondet cs m a) = a
>
>   withUntyped = const
>
> instance (WithUntyped a, cs ~ C a, m ~ M a)
>        => WithUntyped (Nondet cs m b -> a)
>  where
>   type C (Nondet cs m b -> a) = C a
>   type M (Nondet cs m b -> a) = M a
>   type T (Nondet cs m b -> a) = T a
>
>   withUntyped alt (x:xs) = withUntyped (alt (Typed x)) xs
>   withUntyped _ _ = error "LazyNondet.withUntyped: too few arguments"

These instances define the overloaded function `withUntyped` that has
all of the following types at the same time:

    withUntyped :: Nondet cs m a
                -> [Untyped cs m] -> Nondet cs m a

    withUntyped :: (Nondet cs m a -> Nondet cs m b)
                -> [Untyped cs m] -> Nondet cs m b

    withUntyped :: (Nondet cs m a -> Nondet cs m b -> Nondet cs m c)
                -> [Untyped cs m] -> Nondet cs m c
    ...

If the function given as first argument has n arguments, then the
application of `withUntyped` to this function consumes n elements of
the list of untyped values and yields the result of applying the given
function to typed versions of these values.

> newtype Match a cs m b = Match { unMatch :: (ConIndex, cs -> Branch cs m b) }
> data Branch cs m a =
>   forall t . (WithUntyped t, cs ~ C t, m ~ M t, a ~ T t) => Branch t
>
> match :: (ConsRep a, WithUntyped b)
>       => a -> (C b -> b) -> Match t (C b) (M b) (T b)
> match c alt = Match (constrIndex (consRep c), Branch . alt)

The operation `match` is used to build destructor functions for
non-deterministic values that can be used with `caseOf`.

> failure :: MonadPlus m => Nondet cs m a
> failure = Typed mzero

Failure is just a type version of `mzero`.

> caseOf :: (MonadSolve cs m m, MonadConstr Choice m)
>        => Nondet cs m a -> [Match a cs m b] -> cs -> Nondet cs m b
> caseOf x bs = caseOf_ x bs failure
>
> caseOf_ :: (MonadSolve cs m m, MonadConstr Choice m)
>         => Nondet cs m a -> [Match a cs m b] -> Nondet cs m b
>         -> cs -> Nondet cs m b
> caseOf_ x bs def =
>   withHNF x $ \hnf cs ->
>   case hnf of
>     FreeVar _ y -> caseOf_ (Typed y) bs def cs
>     Delayed p res
>       | p cs      -> delayed p (\cs -> caseOf_ (Typed (res cs)) bs def cs)
>       | otherwise -> caseOf_ (Typed (res cs)) bs def cs
>     Cons _ idx args ->
>       maybe def (\b -> branch (b cs) args) (lookup idx (map unMatch bs))
>
> branch :: Branch cs m a -> [Untyped cs m] -> Nondet cs m a
> branch (Branch alt) = withUntyped alt

We provide operations `caseOf_` and `caseOf` (with and without a
default alternative) for more convenient pattern matching. The untyped
values are hidden so functional-logic code does not need to match on
the `Cons` constructor explicitly. However, using this combinator
causes an additional slowdown because of the list lookup. It remains
to be checked how big the slowdown of using `caseOf` is compared to
using `withHNF` directly.

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
