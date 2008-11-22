% Sharing Choices with Constraints
% [Sebastian Fischer](mailto:sebf@informatik.uni-kiel.de)
% November, 2008

We define a constraint store that stores choice constraints which
ensure that shared non-deterministic choices evaluate to the same
values when translating lazy functional logic programs.

Based on this constraint store, we provide a function `choice` that
can be used to generate choices that are constrained to evaluate to
the same value if they are shared.

~~~ { .literatehaskell }

> {-# OPTIONS
>      -XMultiParamTypeClasses
>      -XFlexibleInstances
>      -XFlexibleContexts
>   #-}
>
> module Control.Monad.Constraint.Choice ( choice ) where
>
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Constraint
>
> -- expose `ghc` package in order to be able to import these:
> import Unique
> import UniqSupply
> import UniqFM

~~~

We borrow unique identifiers from the package `ghc` which is hidden by
default.

~~~ { .literatehaskell }

> instance Eq a => ConstraintStore (Unique,a) (UniqFM a)
>  where
>   assert (u,x) = do
>     cs <- get
>     maybe (put (addToUFM_Directly cs u x))
>           (guard . (x==))
>           (lookupUFM_Directly cs u)

~~~

When each choice is labeled with a `Unique`, then we can store
alternatives in a `UniqFM` making it an instance of `ConstraintStore`.

The `assert` operations fails to insert conflicting choices.

~~~ { .literatehaskell }

> choice :: (MonadPlus m, Collect (Unique,Int) m) => Unique -> [m a] -> m a
> choice u = foldr1 mplus . (mzero:) . zipWith constrain [(0::Int)..]
>  where constrain n = (collect (u,n)>>)

~~~

The operation `choice` takes a unique label and a list of monadic
values that can be constrained with choice constraints. The result is
a single monadic action combining the alternatives with `mplus`. If it
occurs more than once in a bigger monadic action, the result is
constrained to take the same alternative everywhere when solving
collected constraints.

