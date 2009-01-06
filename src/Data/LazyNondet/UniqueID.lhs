% Unique Identifiers
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       TypeFamilies,
>       FlexibleContexts,
>       FlexibleInstances,
>       MultiParamTypeClasses
>   #-}
>
> module Data.LazyNondet.UniqueID (
>
>   initID, withUnique
>
> ) where
>
> import Data.LazyNondet.Types
>
> import Control.Monad
>
> import Data.Supply

Non-deterministic computations need a supply of unique identifiers in
order to constrain shared choices.

> initID :: IO ID
> initID = liftM ID newNumSupply
>
> class With x a
>  where
>   type C x a
>   type M x a :: * -> *
>   type T x a
>
>   with :: a -> x -> Nondet (C x a) (M x a) (T x a)
>
> instance With x (Nondet cs m a)
>  where
>   type C x (Nondet cs m a) = cs
>   type M x (Nondet cs m a) = m
>   type T x (Nondet cs m a) = a
>
>   with = const
>
> instance With ID a => With ID (ID -> a)
>  where
>   type C ID (ID -> a) = C ID a
>   type M ID (ID -> a) = M ID a
>   type T ID (ID -> a) = T ID a
>
>   with f (ID us) = with (f (ID l)) (ID r) where (l,r) = split2 us
>
> withUnique :: With ID a => a -> ID -> Nondet (C ID a) (M ID a) (T ID a)
> withUnique = with

We provide an overloaded operation `withUnique` to simplify the
distribution of unique identifiers when defining possibly
non-deterministic operations. Non-deterministic operations have an
additional argument for unique identifiers. The operation `withUnique`
allows to consume an arbitrary number of unique identifiers hiding
their generation. Conceptually, it has all of the following types at
the same time:

    Nondet m a -> ID -> Nondet m a
    (ID -> Nondet m a) -> ID -> Nondet m a
    (ID -> ID -> Nondet m a) -> ID -> Nondet m a
    (ID -> ID -> ID -> Nondet m a) -> ID -> Nondet m a
    ...

We make use of type families because GHC considers equivalent
definitions with functional dependencies illegal due to the overly
restrictive "coverage condition".
