% Basic Types for Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines the basic types to represent lazy
non-deterministic data.

> {-# LANGUAGE
>       PatternGuards,
>       FlexibleInstances
>   #-}
>
> module Data.LazyNondet.Types (
>
>   Context(..), ID(..), 
>
>   NormalForm(..), HeadNormalForm(..), Untyped, Nondet(..),
>
>   mkHNF, freeVar, delayed
>
> ) where
>
> import Data.Data
>
> import Control.Monad.Update
>
> import Data.Supply
>
> newtype Context cs = Context cs
>
> newtype ID = ID (Supply Int)
>
> data NormalForm = NormalForm Constr [NormalForm] | Var Int

The normal form of data is represented by the type `NormalForm` which
defines a tree of constructors and logic variables. The type `Constr`
is a representation of constructors defined in the `Data.Generics`
package. With generic programming we can convert between Haskell data
types and the `NormalForm` type.

> data HeadNormalForm cs m
>   = Cons DataType ConIndex [Untyped cs m]
>   | FreeVar ID (Untyped cs m)
>   | Delayed (Context cs -> Bool) (Context cs -> Untyped cs m)
>   | Lambda (Untyped cs m -> Context cs -> ID -> Untyped cs m)
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
> mkHNF c = Cons (constrType c) (constrIndex c)

In head-normal forms we split the constructor representation into a
representation of the data type and the index of the constructor, to
enable pattern matching on the index.

Free (logic) variables are represented by `FreeVar u x` where `u` is a
uniqe identifier and `x` represents the result of narrowing the
variable according to the constraint store passed to the operation
that creates the variable.

> freeVar :: Monad m => ID -> Nondet cs m a -> Nondet cs m a
> freeVar u = Typed . return . FreeVar u . untyped

The function `freeVar` is used to put a name around a narrowed free
variable.

> delayed :: Monad m => (Context cs -> Bool) -> (Context cs -> Nondet cs m a)
>         -> Nondet cs m a
> delayed p resume = Typed . return . Delayed p $ (untyped . resume)

With `delayed` computations can be delayed to be reexecuted with the
current constraint store whenever they are demanded. This is useful to
avoid unessary branching when narrowing logic variables. Use with
care: `delayed` intentionally destroys sharing!

The first parameter is a predicate on constraint stores that specifies
whether the result of pattern matching the constructed delayed value
should be delayed again.

`Show` Instances
----------------

> instance Show (HeadNormalForm cs [])
>  where
>   show (FreeVar (ID u) _) = '_':show (supplyValue u)
>   show (Delayed _ _) = "<delayed>"
>   show (Cons typ idx args) 
>     | null args = show con
>     | otherwise = unwords (('(':show con):map show args++[")"])
>    where con = indexConstr typ idx
>
> instance Show (Nondet cs [] a)
>  where
>   show = show . untyped
>
> instance Show (Nondet cs (UpdateT cs []) a)
>  where
>   show = show . untyped
>
> instance Show (HeadNormalForm cs (UpdateT cs []))
>  where
>   show (FreeVar (ID u) _)  = '_':show (supplyValue u)
>   show (Delayed _ _)         = "<delayed>"
>   show (Cons typ idx [])   = show (indexConstr typ idx)
>   show (Cons typ idx args) =
>     "("++show (indexConstr typ idx)++" "++unwords (map show args)++")" 

To simplify debugging, we provide `Show` instances for head-normal
forms and non-deterministic values.

> instance Show NormalForm
>  where
>   showsPrec _ (Var u) = ('_':) . shows u
>   showsPrec _ (NormalForm cons []) = shows cons
>   showsPrec n x@(NormalForm cons args)
>     | Just xs <- fromList x = shows xs
>     | n == 0 = shows cons . (' ':) . foldr1 (\y z -> y.(' ':).z)
>                 (map (showsPrec 1) args)
>     | otherwise = ('(':) . shows x . (')':)
>
> fromList :: NormalForm -> Maybe [NormalForm]
> fromList (NormalForm cons args)
>   | show cons == "[]" = Just []
>   | show cons == "(:)", [x,l] <- args, Just xs <- fromList l = Just (x:xs)
> fromList _ = Nothing

For normal forms we provide a custum `Show` instance because we want
to use it to print partial values in the evaluator.
