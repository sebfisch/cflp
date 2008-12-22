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
>   Choice, ChoiceStore(..), ChoiceStoreUnique, noChoices, choice
>
> ) where
>
> import Control.Monad.State
> import Control.Monad.Constraint
>
> import qualified Data.IntMap as IM
>
> class ChoiceStore cs
>  where
>   lookupChoice :: Int -> cs -> Maybe Int

We define an interface for choice stores that provide an operation to
lookup a previously made choice.

> newtype Choice = Choice (Int,Int)
> newtype ChoiceStoreUnique = ChoiceStore (IM.IntMap Int)
>
> noChoices :: ChoiceStoreUnique
> noChoices = ChoiceStore IM.empty
>
> instance ChoiceStore ChoiceStoreUnique
>  where
>   lookupChoice u (ChoiceStore cs) = IM.lookup u cs

A finite map mapping unique identifiers to integers is a
`ChoiceStore`.

> instance ConstraintStore Choice ChoiceStoreUnique
>  where
>   assert (Choice (u,x)) = do
>     ChoiceStore cs <- get
>     maybe (put (ChoiceStore (IM.insert u x cs)))
>           (guard . (x==))
>           (IM.lookup u cs)

Choices are labeled with a unique identifier, so we can store them in
an `IntMap` making it an instance of `ConstraintStore`.

The `assert` operations fails to insert conflicting choices.

> choice :: (MonadConstr Choice m, ChoiceStore cs)
>        => cs -> Int -> [m a] -> m a
> choice cs u xs =
>   maybe (foldr1 mplus . (mzero:) . zipWith constrain [(0::Int)..] $ xs)
>         (xs!!)
>         (lookupChoice u cs)
>  where constrain n = (constr (Choice (u,n))>>)

The operation `choice` takes a unique label and a list of monadic
values that can be constrained with choice constraints. The result is
a single monadic action combining the alternatives with `mplus`. If it
occurs more than once in a bigger monadic action, the result is
constrained to take the same alternative everywhere when collecting
constraints.

If a choice with the same label has been created previously and the
label is already constrained to an alternative, then this alternative
is returned directly and no choice is created.

This situation occurs when a shared logic variable is renarrowed when
it is demanded again during a computation.

