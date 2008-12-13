% Basic Types for Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines the basic types to represent lazy
non-deterministic data together with operations to convert them into
primitive Haskell data and vice versa.

> {-# LANGUAGE
>       FlexibleInstances
>   #-}
>
> module Data.LazyNondet.Types (
>
>   ID(..), NormalForm(..), HeadNormalForm(..), Untyped, Nondet(..),
>
>   mkHNF, freeVar, execute
>
> ) where
>
> import Data.Data
>
> import Control.Monad.Constraint
>
> import UniqSupply
>
> newtype ID = ID UniqSupply
>
> data NormalForm = NormalForm Constr [NormalForm]
>  deriving Show

The normal form of data is represented by the type `NormalForm` which
defines a tree of constructors. The type `Constr` is a representation
of constructors defined in the `Data.Generics` package. With generic
programming we can convert between Haskell data types and the
`NormalForm` type.

> data HeadNormalForm cs m
>   = Cons DataType ConIndex [Untyped cs m]
>   | FreeVar ID (Untyped cs m)
>   | Execute (cs -> Untyped cs m)
>
> type Untyped cs m = m (HeadNormalForm cs m)

Data in lazy functional-logic programs is evaluated on demand. The
evaluation of arguments of a constructor may lead to different
non-deterministic results. Hence, we use a monad around every
constructor in the head-normal form of a value.

> newtype Nondet cs m a = Typed { untyped :: Untyped cs m }

Untyped non-deterministic data can be phantom typed in order to define
logic variables by overloading. The phantom type must be the Haskell
data type that should be used for conversion into primitive data.

> mkHNF :: Constr -> [Untyped cs m] -> HeadNormalForm cs m
> mkHNF c args = Cons (constrType c) (constrIndex c) args

In head-normal forms we split the constructor representation into a
representation of the data type and the index of the constructor, to
enable pattern matching on the index.

Free (logic) variables are represented by `Unknown u x` where `u` is a
uniqe identifier and `x` which represents the result of narrowing the
variable according to the constraint store passed to the operation
that creates the variable.

> freeVar :: Monad m => ID -> Nondet cs m a -> Nondet cs m a
> freeVar u = Typed . return . FreeVar u . untyped

The function `freeVar` is used to put a name around a narrowed free
variable.

> execute :: Monad m => (cs -> Nondet cs m a) -> Nondet cs m a
> execute exe = Typed . return . Execute $ (untyped . exe)

With `execute` computations can be delayed to be rexecuted with the
current constraint store whenever they are demanded. This is useful to
avoid unessary branching when narrowing logic variables. Use with
care: `execute` intentionally destroys sharing!

`Show` Instances
----------------

> instance Show (HeadNormalForm cs [])
>  where
>   show (FreeVar (ID u) _) = show (uniqFromSupply u)
>   show (Execute _) = "<delayed>"
>   show (Cons typ idx args) 
>     | null args = show con
>     | otherwise = unwords (("("++show con):map show args++[")"])
>    where con = indexConstr typ idx
>
> instance Show (Nondet cs [] a)
>  where
>   show = show . untyped
>
> instance Show (Nondet cs (ConstrT cs []) a)
>  where
>   show = show . untyped
>
> instance Show (HeadNormalForm cs (ConstrT cs []))
>  where
>   show (FreeVar (ID u) _)  = show (uniqFromSupply u)
>   show (Execute _)         = "<delayed>"
>   show (Cons typ idx [])   = show (indexConstr typ idx)
>   show (Cons typ idx args) =
>     "("++show (indexConstr typ idx)++" "++unwords (map show args)++")" 

To simplify debugging, we provide `Show` instances for head-normal
forms and non-deterministic values.

