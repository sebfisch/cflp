% Lazy Non-Deterministic Data
% [Sebastian Fischer](mailto:sebf@informatik.uni-kiel.de)
% November, 2008

We define a datatype with operations for lazy non-deterministic
programming.

~~~ { .literatehaskell }

> {-# OPTIONS_GHC
>      -XMultiParamTypeClasses
>      -XFlexibleContexts
>      -XFlexibleInstances
>   #-}
>
> module Data.LazyNondet where
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

~~~

We borrow unique identifiers from the package `ghc` which is hidden by
default.

~~~ { .literatehaskell }

> data NormalForm = NormalForm ConsName [NormalForm]
> type ConsName   = Int

~~~

The normal form of data is represented by the type `NormalForm` which
defines a Tree of constructors.

~~~ { .literatehaskell }

> data HeadNormalForm m = Cons ConsName [Untyped m]
> type Untyped m = m (HeadNormalForm m)

~~~

Data in lazy functional-logic programs is evaluated on demand. The
evaluation of arguments of a constructor may lead to different
non-deterministic results. Hence, we use a monad around every
constructor in the head-normal form of a value.

~~~ { .literatehaskell }

> newtype Typed a m = Typed { untyped :: Untyped m }

~~~

Untyped non-deterministic data can be phantom typed in order to define
logic variables by overloading.

~~~ { .literatehaskell }

> type ND a m = UniqSupply -> Typed a m

~~~

Non-deterministic computations need a supply of unique identifiers in
order to constrain shared choices.

~~~ { .literatehaskell }

> class WithUnique a b
>  where
>   withUnique :: a -> UniqSupply -> b
>
> instance WithUnique (Typed a m) (Typed a m)
>  where
>   withUnique x _ = x
>
> instance WithUnique a b => WithUnique (UniqSupply -> a) b
>  where
>   withUnique f us = withUnique (f vs) ws
>    where (vs,ws) = splitUniqSupply us

~~~

We provide an operation `withUnique` to simplify the distribution of
unique identifiers.

~~~ { .literatehaskell }

> class Nondet a
>  where
>   unknown :: ND a m

~~~

Phantom types that are used to type non-deterministc data, need to be
instances of the class `Nondet`. The operation `unknown` then
represents a logic variable of the corresponding type.

~~~ { .literatehaskell }

> oneOf :: MonadConstr (Unique,Int) m => [Typed a m] -> ND a m
> oneOf xs us = Typed (choice (uniqFromSupply us) (map untyped xs))

~~~

The operation `oneOf` takes a list of type non-deterministic values
and returns a non-deterministic value that yields on of the lists
elements.

~~~ { .literatehaskell }

> caseOf :: (Monad (t cs m), RunConstr cs m t)
>        => cs -> Typed a (t cs m)
>        -> (cs -> HeadNormalForm (t cs m) -> Typed b (t cs m))
>        -> Typed b (t cs m)
> caseOf cs x branch = Typed (match cs (untyped x) ((untyped.).branch))
>
> match :: (Monad (t cs m), RunConstr cs m t)
>       => cs -> Untyped (t cs m)
>       -> (cs -> HeadNormalForm (t cs m) -> Untyped (t cs m))
>       -> Untyped (t cs m)
> match cs x branch = do
>   (hnf, cs') <- lift (runStateT (runConstr x) cs)
>   branch cs' hnf

~~~

The `caseOf` operation is used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value.

~~~ { .literatehaskell }

> normalForm :: RunConstr cs m t => Typed a (t cs m) -> cs -> m NormalForm
> normalForm = evalStateT . nf . untyped
>
> nf :: RunConstr cs m t => Untyped (t cs m) -> StateT cs m NormalForm
> nf x = do
>   Cons name args <- runConstr x
>   nfs <- mapM nf args
>   return (NormalForm name nfs)

~~~

The `normalForm` function evaluates a non-deterministic value and
lifts all non-deterministic choices to the top level. In the results,
arguments of constructors are always deterministic.


