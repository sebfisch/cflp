% Sharing Choices with Constraints
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

We define a constraint store that stores choice constraints which
ensure that shared non-deterministic choices evaluate to the same
values when translating lazy functional logic programs.

Based on this constraint store, we provide a function `choice` that
can be used to generate choices that are constrained to evaluate to
the same value if they are shared.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts
>   #-}
>
> module Control.Monad.Constraint.Choice (
>
>   Choice, ChoiceStore, noChoices, choice
>
> ) where
>
> import Control.Monad.State
> import Control.Monad.Constraint
>
> import Unique
> import UniqFM

We borrow unique identifiers from the package `ghc` which is hidden by
default.

> newtype Choice = Choice (Unique,Int)
> newtype ChoiceStore = ChoiceStore (UniqFM Int)
>
> noChoices :: ChoiceStore
> noChoices = ChoiceStore emptyUFM
>
> instance ConstraintStore Choice ChoiceStore
>  where
>   assert (Choice (u,x)) = do
>     ChoiceStore cs <- get
>     maybe (put (ChoiceStore (addToUFM_Directly cs u x)))
>           (guard . (x==))
>           (lookupUFM_Directly cs u)

Choices are labeled with a `Unique`, so we can store them in a
`UniqFM` making it an instance of `ConstraintStore`.

The `assert` operations fails to insert conflicting choices.

> choice :: MonadConstr Choice m => Unique -> [m a] -> m a
> choice u = foldr1 mplus . (mzero:) . zipWith constrain [(0::Int)..]
>  where constrain n = (constr (Choice (u,n))>>)

The operation `choice` takes a unique label and a list of monadic
values that can be constrained with choice constraints. The result is
a single monadic action combining the alternatives with `mplus`. If it
occurs more than once in a bigger monadic action, the result is
constrained to take the same alternative everywhere when collecting
constraints.

