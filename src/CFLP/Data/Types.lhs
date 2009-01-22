% Basic Types for Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines the basic types to represent lazy
non-deterministic data.

> {-# LANGUAGE
>       PatternGuards,
>       FlexibleInstances
>   #-}
>
> module CFLP.Data.Types (
>
>   Context(..), ID(..), 
>
>   ConsLabel(..), NormalForm(..), HeadNormalForm(..), Untyped, Nondet(..),
>
>   freeVar, delayed
>
> ) where
>
> import Data.Supply
>
> import CFLP.Control.Monad.Update
>
> newtype Context cs = Context cs
>
> newtype ID = ID (Supply Int)
>
> data NormalForm
>   = Data ConsLabel [NormalForm]
>   | Var  Int
>   | Fun  (NormalForm -> NormalForm)
>
> data ConsLabel = ConsLabel { index :: Int, name :: String }
>
> instance Show ConsLabel
>  where
>   showsPrec _ = (++) . name

The normal form of data is represented by the type `NormalForm` which
defines a tree of constructors and logic variables or functions.

> data HeadNormalForm cs m
>   = Cons ConsLabel [Untyped cs m]
>   | FreeVar ID (Untyped cs m)
>   | Delayed (Context cs -> m Bool) (Context cs -> Untyped cs m)
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

Free (logic) variables are represented by `FreeVar u x` where `u` is a
uniqe identifier and `x` represents the result of narrowing the
variable according to the constraint store passed to the operation
that creates the variable.

> freeVar :: Monad m => ID -> Nondet cs m a -> Nondet cs m a
> freeVar u = Typed . return . FreeVar u . untyped

The function `freeVar` is used to put a name around a narrowed free
variable.

> delayed :: Monad m => (Context cs -> m Bool) -> (Context cs -> Nondet cs m a)
>         -> Nondet cs m a
> delayed p resume = Typed . return . Delayed p $ (untyped . resume)

With `delayed` computations can be delayed to be reexecuted with the
current constraint store whenever they are demanded. This is useful to
avoid unessary branching when narrowing logic variables. Use with
care: `delayed` intentionally destroys sharing!

The first parameter is a predicate on constraint stores that specifies
whether the result of pattern matching the constructed delayed value
is narrowed w.r.t. the current evaluation context. If it is not,
pattern matching on it will be delayed again.

`Show` Instances
----------------

> instance Show (HeadNormalForm cs [])
>  where
>   show (FreeVar (ID u) _) = '_':show (supplyValue u)
>   show (Delayed _ _) = "<delayed>"
>   show (Lambda _) = "<function>"
>   show (Cons label args) 
>     | null args = show label
>     | otherwise = unwords (('(':show label):map show args++[")"])
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
>   show (FreeVar (ID u) _) = '_':show (supplyValue u)
>   show (Delayed _ _)      = "<delayed>"
>   show (Lambda _)         = "<function>"
>   show (Cons label [])    = show label
>   show (Cons label args)  =
>     "("++show label++" "++unwords (map show args)++")" 

To simplify debugging, we provide `Show` instances for head-normal
forms and non-deterministic values.

> instance Show NormalForm
>  where
>   showsPrec _ (Var u) = ('_':) . shows u
>   showsPrec _ (Fun _) = ("<function>"++)
>   showsPrec _ (Data label []) = shows label
>   showsPrec n x@(Data label args)
>     | Just xs <- fromList x = shows xs
>     | n == 0 = shows label . (' ':) . foldr1 (\y z -> y.(' ':).z)
>                 (map (showsPrec 1) args)
>     | otherwise = ('(':) . shows x . (')':)
>
> fromList :: NormalForm -> Maybe [NormalForm]
> fromList (Data label args)
>   | show label == "[]" = Just []
>   | show label == "(:)", [x,l] <- args, Just xs <- fromList l = Just (x:xs)
> fromList _ = Nothing

For normal forms we provide a custum `Show` instance because we want
to use it to print partial values in the evaluator.
