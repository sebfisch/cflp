% Pattern Matching of Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       RankNTypes,
>       TypeFamilies,
>       FlexibleContexts,
>       FlexibleInstances,
>       ExistentialQuantification
>   #-}
>
> module Data.LazyNondet.Matching (
>
>   Match, match, withHNF, caseOf, caseOf_
>
> ) where
>
> import Data.Data
> import Data.LazyNondet.Types
> import Data.LazyNondet.Combinators
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

> newtype Match cs m a b = Match { unMatch :: (ConIndex, cs -> Branch cs m b) }
> data Branch cs m a =
>   forall t . (WithUntyped t, cs ~ C t, m ~ M t, a ~ T t) => Branch t
>
> match :: (ConsRep a, WithUntyped b)
>       => a -> (C b -> b) -> Match (C b) (M b) t (T b)
> match c alt = Match (constrIndex (consRep c), Branch . alt)

The operation `match` is used to build destructor functions for
non-deterministic values that can be used with `caseOf`.

> caseOf :: (MonadSolve cs m m, MonadConstr Choice m)
>        => Nondet cs m a -> [Match cs m a b] -> cs -> Nondet cs m b
> caseOf x bs = caseOf_ x bs failure
>
> caseOf_ :: (MonadSolve cs m m, MonadConstr Choice m)
>         => Nondet cs m a -> [Match cs m a b] -> Nondet cs m b
>         -> cs -> Nondet cs m b
> caseOf_ x bs def =
>   withHNF x $ \hnf cs ->
>   case hnf of
>     FreeVar _ y -> caseOf_ (Typed y) bs def cs
>     Execute exe -> caseOf_ (Typed (exe cs)) bs def cs
>     Cons _ idx args ->
>       maybe def (\b -> branch (b cs) args) (lookup idx (map unMatch bs))
>
> branch :: Branch cs m a -> [Untyped cs m] -> Nondet cs m a
> branch (Branch alt) = withUntyped alt

We provide operations `caseOf` and `caseOf` (with and without a
default alternative) for more convenient pattern matching. The untyped
values are hidden so functional-logic code does not need to match on
the `Cons` constructor explicitly. However, using this combinator
causes an additional slowdown because of the list lookup. It remains
to be checked how big the slowdown of using `caseOf` is compared to
using `withHNF` directly.

