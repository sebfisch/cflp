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
> module Control.Constraint.Choice (
>
>   ChoiceStore(..), ChoiceStoreIM, noChoices, labeledChoices
>
> ) where
>
> import Control.Monad.State
> import Control.Monad.Update
>
> import qualified Data.IntMap as IM
>
> class ChoiceStore c
>  where
>   lookupChoice :: Int -> c -> Maybe Int
>   assertChoice :: MonadPlus m => c -> Int -> Int -> c -> m c

We define an interface for choice stores that provide an operation to
lookup a previously made choice. The first argument of `assertChoice`
is a dummy argument to fix the type of the store in partial
applications.


> newtype ChoiceStoreIM = ChoiceStoreIM (IM.IntMap Int) deriving Show
>
> noChoices :: ChoiceStoreIM
> noChoices = ChoiceStoreIM IM.empty
>
> instance ChoiceStore ChoiceStoreIM
>  where
>   lookupChoice u (ChoiceStoreIM cs) = IM.lookup u cs
>
>   assertChoice _ u x (ChoiceStoreIM cs) =
>     maybe (return (ChoiceStoreIM (IM.insert u x cs)))
>           (\y -> do guard (x==y); return (ChoiceStoreIM cs))
>           (IM.lookup u cs)

A finite map mapping unique identifiers to integers is a
`ChoiceStore`. The `assertChoice` operations fails to insert
conflicting choices.

> labeledChoices :: (Monad m, ChoiceStore c, MonadUpdate c m)
>                => c -> Int -> [m a] -> [m a]
> labeledChoices c u xs =
>   maybe (zipWith constrain [(0::Int)..] xs)
>         ((:[]).(xs!!))
>         (lookupChoice u c)
>  where constrain n = (update (assertChoice c u n)>>)

The operation `labelChoices` takes a unique label and a list of
monadic values that can be constrained with choice constraints. The
result is a list of monadic actions that are constrained to take the
same alternative at every shared occurrence when collecting
constraints.

If a choice with the same label has been created previously and the
label is already constrained to an alternative, then this alternative
is returned directly and no choice is created.

This situation occurs when a shared logic variable is renarrowed when
it is demanded again during a computation.

