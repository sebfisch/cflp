% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% November, 2008

This module provides a datatype with operations for lazy
non-deterministic programming.

> {-# OPTIONS
>      -XMultiParamTypeClasses
>      -XFlexibleContexts
>      -XFlexibleInstances
>      -XTypeFamilies
>   #-}
>
> module Data.LazyNondet (
>
>   NormalForm, HeadNormalForm(..), cons, Typed(..),
>
>   ID, initID, WithUnique(..), 
>
>   Unknown(..), failure, oneOf, caseOf,
>
>   Data, normalForm
>
> ) where
>
> import Data.Generics
>
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Trans
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> -- expose `ghc` package in order to be able to import these:
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
> cons :: Constr -> [Untyped m] -> HeadNormalForm m
> cons c args = Cons (constrType c) (constrIndex c) args
>
> instance Show (HeadNormalForm [])
>  where
>   show (Cons typ idx args) 
>     | null args = show con
>     | otherwise = unwords (("("++show con):map show args++[")"])
>    where con = indexConstr typ idx

Data in lazy functional-logic programs is evaluated on demand. The
evaluation of arguments of a constructor may lead to different
non-deterministic results. Hence, we use a monad around every
constructor in the head-normal form of a value.

In head-normal forms we split the constructor representation into a
representation of the data type and the index of the constructor, to
enable pattern matching on the index.

> newtype Typed m a = Typed { untyped :: Untyped m }
>
> instance Show (Typed [] a)
>  where
>   show = show . untyped

Untyped non-deterministic data can be phantom typed in order to define
logic variables by overloading. The phantom type must be the Haskell
data type that should be used for conversion.


Threading Unique Identifiers and a Constraint Store
---------------------------------------------------

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
>   withUnique :: a -> ID -> Typed (Mon a) (Typ a)
>
> instance WithUnique (Typed m a)
>  where
>   type Mon (Typed m a) = m
>   type Typ (Typed m a) = a
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

We provide an operation `withUnique` to simplify the distribution of
unique identifiers when defining possibly non-deterministic
operations. Non-deterministic operations have an additional arguments
for unique identifiers. The operation `withUnique` allows to consume
an arbitrary number of unique identifiers hiding their generation.

We make use of type families because GHC considers equivalent
definitions with functional dependencies illegal ("the coverage
condition fails").


Combinators for Functional-Logic Programming
--------------------------------------------

> class Unknown a
>  where
>   unknown :: MonadConstr Choice m => ID -> Typed m a

The application of `unknown` to a unique identifier represents a logic
variable of the corresponding type.

> oneOf :: MonadConstr Choice m => [Typed m a] -> ID -> Typed m a
> oneOf xs us = Typed (choice (uniqFromSupply us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.

> failure :: MonadPlus m => Typed m a
> failure = Typed mzero

A failing computation could be defined using `oneOf`, but we provide a
special combinator that does not need a supply of unique identifiers.

> caseOf :: (Monad (t cs m), RunConstr cs m t)
>        => Typed (t cs m) a
>        -> (HeadNormalForm (t cs m) -> cs -> Typed (t cs m) b)
>        -> cs -> Typed (t cs m) b
> caseOf x branch cs = Typed (do
>   (hnf,cs') <- lift (runStateT (runConstr (untyped x)) cs)
>   untyped (branch hnf cs'))

The `caseOf` operation is used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value.


Converting Between Primitive and Non-Deterministic Data
-------------------------------------------------------

> primitive :: Data a => NormalForm -> a
> primitive (NormalForm con args) =
>   snd (gmapAccumT perkid args (fromConstr con))
>  where
>   perkid (t:ts) _ = (ts, primitive t)
>
> generic :: Data a => a -> NormalForm
> generic x = NormalForm (toConstr x) (gmapQ generic x)
>
> nondet :: Monad m => NormalForm -> Untyped m
> nondet (NormalForm con args) = return (cons con (map nondet args))
>
> typed :: (Monad m, Data a) => a -> Typed m a
> typed = Typed . nondet . generic

We provide generic operations to convert between instances of the
`Data` class and non-deterministic data.

> normalForm :: (RunConstr cs m t, Data a) => Typed (t cs m) a -> cs -> m a
> normalForm x cs = liftM primitive $ evalStateT (nf (untyped x)) cs
>
> nf :: RunConstr cs m t => Untyped (t cs m) -> StateT cs m NormalForm
> nf x = do
>   Cons typ idx args <- runConstr x
>   nfs <- mapM nf args
>   return (NormalForm (indexConstr typ idx) nfs)

The `normalForm` function evaluates a non-deterministic value and
lifts all non-deterministic choices to the top level. The results are
deterministic values and can be converted into their Haskell
representation.

