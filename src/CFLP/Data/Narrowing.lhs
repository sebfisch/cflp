% Logic Variables and Narrowing
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       FlexibleContexts,
>       FlexibleInstances,
>       MultiParamTypeClasses
>   #-}
>
> module CFLP.Data.Narrowing (
>
>   unknown, Narrow(..), -- Binding(..), narrowVar, 
>
>   (?), oneOf
>
> ) where
>
> import Data.Supply
>
> import Control.Monad
>
> import CFLP.Data.Types
>
> import CFLP.Control.Monad.Update
> import CFLP.Control.Strategy

The application of `unknown` to a constraint store and a unique
identifier represents a logic variable of an arbitrary type. 

> unknown :: (Monad s, Strategy c s, MonadUpdate c s, Update c s s, Narrow c a)
>         => ID -> Nondet c s a
> unknown u = freeVar u (delayed (isNarrowedID u) (`narrow`u))
>
> isNarrowedID :: Strategy c s => ID -> Context c -> s Bool
> isNarrowedID (ID us) (Context c) = isNarrowed c (supplyValue us)

Logic variables of type `a` can be narrowed to head-normal form if
there is an instance of the type class `Narrow`. A constraint store
may be used to find the possible results which are returned in a monad
that supports choices. Usually, `narrow` will be implemented as a
non-deterministic generator using `oneOf`, but for specific types
different strategies may be implemented.

> class Narrow c a
>  where
>   narrow :: (Monad s, Strategy c s, MonadUpdate c s, Update c s s)
>          => Context c -> ID -> Nondet c s a

The operator `(?)` wraps the combinator `oneOf` to generate a delayed
non-deterministic choice that is executed whenever it is
demanded. Although the choice itself is reexecuted according to the
current constraint store, the arguments of `(?)` are shared among all
executions and *not* reexecuted.

> (?) :: (Monad s, Strategy c s, MonadUpdate c s)
>     => Nondet c s a -> Nondet c s a -> ID -> Nondet c s a
> (x ? y) u = delayed (isNarrowedID u) (\c -> oneOf [x,y] c u)

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.

> oneOf :: (Strategy c s, MonadUpdate c s)
>       => [Nondet c s a] -> Context c -> ID -> Nondet c s a
> oneOf xs (Context c) (ID us)
>   = Typed (choose c (supplyValue us) (map untyped xs))


Constraint Solving
------------------

We provide a type class for constraint stores that support branching
on variables.

 class Solver c
  where
   branchOn :: MonadPlus m => c -> Int -> c -> m c

The first argument of `branchOn` is only used to support the type
checker. It must be ignored when instantiating the `Solver` class.

The type class `Binding` defines a function that looks up a variable
binding in a constraint store.

 class Binding c a
  where
   binding :: (Monad m, Update cs m m) => c -> Int -> Maybe (Nondet cs m a)

The result of the `binding` function is optional in order to allow for
composing results when transforming evaluation contexts.

The base instance for the unit context always returns `Nothing`:

 instance Binding () a where binding _ _ = Nothing

We provide a default implementation of the `narrow` function for
constraint solvers that support variable lookups. This function can be
used to define the `Narrow` instance for types that are handled by
constraint solvers.

 narrowVar :: (Monad s, Strategy c s, MonadUpdate c s, 
               Update c s s, Narrow a, Solver c, Binding c a)
           => Context c -> ID -> Nondet c s a
 narrowVar (Context c) u@(ID us) = joinNondet $ do
   let v = supplyValue us
   isn <- isNarrowed c v
   if isn
    then maybe (error "no binding for narrowed variable") return (binding c v)
    else do
     update (branchOn c v)
     return (unknown u)

An evaluation context that is a `Solver` or supports `Binding` can be
transformed without losing this functionality.

 instance (Solver c, Transformer t) => Solver (t c)
  where
   branchOn _ = inside . branchOn undefined

 instance (Binding c a, Transformer t) => Binding (t c) a
  where
   binding = binding . project

