% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a datatype with operations for lazy
non-deterministic programming.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies
>   #-}
>
> module Data.LazyNondet (
>
>   NormalForm, HeadNormalForm(..), mkHNF, Nondet(..),
>
>   ID, initID, WithUnique(..), 
>
>   Unknown(..), failure, oneOf, caseOf,
>
>   Data, normalForm
>
> ) where
>
> import Data.Data
> import Data.Generics.Twins ( gmapAccumT )
>
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Trans
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> import Unique
> import UniqSupply
> import UniqFM

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

> type ID = UniqSupply
>
> initID :: IO ID
> initID = mkSplitUniqSupply 'x'
>
> class WithUnique a
>  where
>   type Mon a :: * -> *
>   type Typ a
>
>   withUnique :: a -> ID -> Nondet (Mon a) (Typ a)
>
> instance WithUnique (Nondet m a)
>  where
>   type Mon (Nondet m a) = m
>   type Typ (Nondet m a) = a
>
>   withUnique = const
>
> instance WithUnique a => WithUnique (ID -> a)
>  where
>   type Mon (ID -> a) = Mon a
>   type Typ (ID -> a) = Typ a
>
>   withUnique f us = withUnique (f vs) ws
>    where (vs,ws) = splitUniqSupply us

We provide an overloaded operation `withUnique` to simplify the
distribution of unique identifiers when defining possibly
non-deterministic operations. Non-deterministic operations have an
additional argument for unique identifiers. The operation `withUnique`
allows to consume an arbitrary number of unique identifiers hiding
their generation. Conceptually, it has all of the following types at
once:

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
> oneOf xs us = Typed (choice (uniqFromSupply us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.

> failure :: MonadPlus m => Nondet m a
> failure = Typed mzero

A failing computation could be defined using `oneOf`, but we provide a
special combinator that does not need a supply of unique identifiers.

> caseOf :: (Monad m, MonadSolve cs m m)
>        => Nondet m a
>        -> (HeadNormalForm m -> cs -> Nondet m b)
>        -> cs -> Nondet m b
> caseOf x branch cs = Typed (do
>   (hnf,cs') <- runStateT (solve (untyped x)) cs
>   untyped (branch hnf cs'))

The `caseOf` operation is used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value. An updated constraint store is passed to the computation of the
branch function. Collected constraints are kept attached to the
computed value by using an appropriate instance of `MonadSolve` that
does not eliminate them.

Converting Between Primitive and Non-Deterministic Data
-------------------------------------------------------

> prim :: Data a => NormalForm -> a
> prim (NormalForm con args) =
>   snd (gmapAccumT perkid args (fromConstr con))
>  where
>   perkid (t:ts) _ = (ts, prim t)
>
> generic :: Data a => a -> NormalForm
> generic x = NormalForm (toConstr x) (gmapQ generic x)
>
> hnf :: Monad m => NormalForm -> Untyped m
> hnf (NormalForm con args) = return (mkHNF con (map hnf args))
>
> nondet :: (Monad m, Data a) => a -> Nondet m a
> nondet = Typed . hnf . generic

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

