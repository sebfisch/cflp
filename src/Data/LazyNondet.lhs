% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a datatype with operations for lazy
non-deterministic programming.

> {-# LANGUAGE
>       ExistentialQuantification,
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies,
>       FunctionalDependencies
>   #-}
>
> module Data.LazyNondet (
>
>   NormalForm, HeadNormalForm(..), mkHNF, Nondet(..),
>
>   ID, initID, withUnique,
>
>   Unknown(..), failure, oneOf, withHNF, caseOf, caseOf_, Branch(..),
>
>   Data, nondet, normalForm,
>
>   DataConstr(..), cons, branch
>
> ) where
>
> import Data.Data
> import Data.Generics.Twins ( gmapAccumT )
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> import UniqSupply

We borrow unique identifiers from the package `ghc` which is hidden by
default.

> data NormalForm = NormalForm Constr [NormalForm]
>  deriving Show

The normal form of data is represented by the type `NormalForm` which
defines a tree of constructors. The type `Constr` is a representation
of constructors defined in the `Data.Generics` package. With generic
programming we can convert between Haskell data types and the
`NormalForm` type.

> data HeadNormalForm m = Cons DataType ConIndex [Untyped m]
> type Untyped m = m (HeadNormalForm m)
>
> mkHNF :: Constr -> [Untyped m] -> HeadNormalForm m
> mkHNF c args = Cons (constrType c) (constrIndex c) args

Data in lazy functional-logic programs is evaluated on demand. The
evaluation of arguments of a constructor may lead to different
non-deterministic results. Hence, we use a monad around every
constructor in the head-normal form of a value.

In head-normal forms we split the constructor representation into a
representation of the data type and the index of the constructor, to
enable pattern matching on the index.

> newtype Nondet m a = Typed { untyped :: Untyped m }

Untyped non-deterministic data can be phantom typed in order to define
logic variables by overloading. The phantom type must be the Haskell
data type that should be used for conversion.

Threading Unique Identifiers
----------------------------

Non-deterministic computations need a supply of unique identifiers in
order to constrain shared choices.

> newtype ID = ID UniqSupply
>
> initID :: IO ID
> initID = liftM ID $ mkSplitUniqSupply 'x'
>
> class With x a
>  where
>   type Mon x a :: * -> *
>   type Typ x a
>
>   with :: a -> x -> Nondet (Mon x a) (Typ x a)
>
> instance With x (Nondet m a)
>  where
>   type Mon x (Nondet m a) = m
>   type Typ x (Nondet m a) = a
>
>   with = const
>
> instance With ID a => With ID (ID -> a)
>  where
>   type Mon ID (ID -> a) = Mon ID a
>   type Typ ID (ID -> a) = Typ ID a
>
>   with f (ID us) = withUnique (f (ID vs)) (ID ws)
>    where (vs,ws) = splitUniqSupply us
>
> withUnique :: With ID a => a -> ID -> Nondet (Mon ID a) (Typ ID a)
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

Combinators for Functional-Logic Programming
--------------------------------------------

> class Unknown a
>  where
>   unknown :: MonadConstr Choice m => ID -> Nondet m a

The application of `unknown` to a unique identifier represents a logic
variable of the corresponding type.

> oneOf :: MonadConstr Choice m => [Nondet m a] -> ID -> Nondet m a
> oneOf xs (ID us) = Typed (choice (uniqFromSupply us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.

> failure :: MonadPlus m => Nondet m a
> failure = Typed mzero

A failing computation could be defined using `oneOf`, but we provide a
special combinator that does not need a supply of unique identifiers.

> withHNF :: (Monad m, MonadSolve cs m m)
>         => Nondet m a
>         -> (HeadNormalForm m -> cs -> Nondet m b)
>         -> cs -> Nondet m b
> withHNF x branch cs = Typed (do
>   (hnf,cs') <- runStateT (solve (untyped x)) cs
>   untyped (branch hnf cs'))

The `withHNF` operation can be used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value. An updated constraint store is passed to the computation of the
branch function. Collected constraints are kept attached to the
computed value by using an appropriate instance of `MonadSolve` that
does not eliminate them.

> caseOf :: MonadSolve cs m m
>        => Nondet m a -> [(ConIndex, cs -> Branch m b)] -> cs -> Nondet m b
> caseOf x bs = caseOf_ x bs failure
>
> caseOf_ :: MonadSolve cs m m
>         => Nondet m a -> [(ConIndex, cs -> Branch m b)] -> Nondet m b
>         -> cs -> Nondet m b
> caseOf_ x bs def =
>   withHNF x $ \ (Cons _ idx args) cs ->
>                  maybe def (\b -> match (b cs) args) (lookup idx bs)
>
> data Branch m a = forall t . (WithUntyped t, m ~ M t, a ~ T t) => Branch t
>
> match :: Branch m a -> [Untyped m] -> Nondet m a
> match (Branch alt) = withUntyped alt

We provide operations `caseOf` and `caseOf` (with and without a
default alternative) for more convenient pattern matching. The untyped
values are hidden so functional-logic code does not need to match on
the `Cons` constructor explicitly. However, using this combinator
causes an additional slowdown because of the list lookup. It remains
to be checked how big the slowdown of using `caseOf` is compared to
using `withHNF` directly.

> class WithUntyped a
>  where
>   type M a :: * -> *
>   type T a
>
>   withUntyped :: a -> [Untyped (M a)] -> Nondet (M a) (T a)

We repeat the definition of the type class `With` because the current
implementation of GHC does not allow equality constraints in
super-class constraints. We would prefer to define this class as
follows:

    class (With [Untyped m] a, m ~ Mon [Untyped m] a) => WithUnique a
     where
      withUnique :: a -> [Untyped m] -> Nondet m (Typ [Untyped m] a)
      withUnique = with

So it is just a copy of the type class `With` where the argument type
is specialized to use the same monad.

> instance WithUntyped (Nondet m a)
>  where
>   type M (Nondet m a) = m
>   type T (Nondet m a) = a
>
>   withUntyped = const
>
> instance (WithUntyped a, m ~ M a) => WithUntyped (Nondet m b -> a)
>  where
>   type M (Nondet m b -> a) = M a
>   type T (Nondet m b -> a) = T a
>
>   withUntyped alt (x:xs) = withUntyped (alt (Typed x)) xs
>   withUntyped _ _ = error "LazyNondet.withUntyped: too few arguments"

These instances define the overloaded function `withUntyped` that has
all of the following types at the same time:

    withUntyped :: Nondet m a -> [Untyped m] -> Nondet m a
    withUntyped :: (Nondet m a -> Nondet m b) -> [Untyped m] -> Nondet m b
    ...

If the function given as first argument has n arguments, then the
application of `withUntyped` to this function consumes n elements of
the list of untyped values.

Converting Between Primitive and Non-Deterministic Data
-------------------------------------------------------

> prim :: Data a => NormalForm -> a
> prim (NormalForm con args) =
>   snd (gmapAccumT perkid args (fromConstr con))
>  where
>   perkid ts _ = (tail ts, prim (head ts))
>
> generic :: Data a => a -> NormalForm
> generic x = NormalForm (toConstr x) (gmapQ generic x)
>
> nf2hnf :: Monad m => NormalForm -> Untyped m
> nf2hnf (NormalForm con args) = return (mkHNF con (map nf2hnf args))
>
> nondet :: (Monad m, Data a) => a -> Nondet m a
> nondet = Typed . nf2hnf . generic

We provide generic operations to convert between instances of the
`Data` class and non-deterministic data.

> normalForm :: (MonadSolve cs m m', Data a) => Nondet m a -> cs -> m' a
> normalForm x cs = liftM prim $ evalStateT (nf (untyped x)) cs
>
> nf :: MonadSolve cs m m' => Untyped m -> StateT cs m' NormalForm
> nf x = do
>   Cons typ idx args <- solve x
>   nfs <- mapM nf args
>   return (NormalForm (indexConstr typ idx) nfs)

The `normalForm` function evaluates a non-deterministic value and
lifts all non-deterministic choices to the top level. The results are
deterministic values and can be converted into their Haskell
representation.

Syntactic Sugar for Datatype Declarations
-----------------------------------------

> class MkCons m a b | b -> m
>  where
>   mkCons :: a -> [Untyped m] -> b
>
> instance (Monad m, Data a) => MkCons m a (Nondet m t)
>  where
>   mkCons c args = Typed (return (mkHNF (toConstr c) (reverse args)))
>
> instance MkCons m b c => MkCons m (a -> b) (Nondet m t -> c)
>  where
>   mkCons c xs x = mkCons (c undefined) (untyped x:xs)
>
> cons :: MkCons m a b => a -> b
> cons c = mkCons c []

The overloaded operation `cons` takes a Haskell constructor and yields
a corresponding constructor function for non-deterministic values.

> branch :: (DataConstr a, WithUntyped b)
>        => a -> (cs -> b) -> (ConIndex, cs -> Branch (M b) (T b))
> branch c alt = (constrIndex (dataConstr c), Branch . alt)

The operation `branch` is used to build destructor functions for
non-deterministic values that can be used with `caseOf`.

> class DataConstr a
>  where
>   dataConstr :: a -> Constr
>
> instance DataConstr b => DataConstr (a -> b)
>  where
>   dataConstr c = dataConstr (c undefined)

We provide an overloaded operation `dataConstr` that yields a `Constr`
representation for a constructor rather than for a constructed value
like `Data.Data.toConstr` does. We do not provide the base instance

    instance Data a => DataConstr a
     where
      dataConstr = toConstr

because this would require to allow undecidable instances. As a
consequence, specialized base instances need to be defined for every
used datatype. See `Data.LazyNondet.List` for an example of how to use
`dataConstr` to get the representation of polymorphic constructors.

`Show` Instances
----------------

> instance Show (HeadNormalForm [])
>  where
>   show (Cons typ idx args) 
>     | null args = show con
>     | otherwise = unwords (("("++show con):map show args++[")"])
>    where con = indexConstr typ idx
>
> instance Show (Nondet [] a)
>  where
>   show = show . untyped
>
> instance Show (Nondet (ConstrT cs []) a)
>  where
>   show = show . untyped
>
> instance Show (HeadNormalForm (ConstrT cs []))
>  where
>   show (Cons typ idx [])   = show (indexConstr typ idx)
>   show (Cons typ idx args) =
>     "("++show (indexConstr typ idx)++" "++unwords (map show args)++")" 

To simplify debugging, we provide `Show` instances for head-normal
forms and non-deterministic values.

