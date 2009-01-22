% Call-Time Choice as Strategy Transformer
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module implements call-time choice semantics of non-deterministic
programs as a strategy transformer.

We define a constraint store that stores choice constraints which
ensure that shared non-deterministic choices evaluate to the same
values when translating lazy functional logic programs.

Based on this constraint store, we provide a strategy transformer that
can be used to generate choices whose alternatives are constrained to
evaluate to the same value in every shared occurrence.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies
>   #-}
>
> module CFLP.Strategies.CallTimeChoice where
>
> import Data.Maybe
> import qualified Data.IntMap as IM
>
> import Control.Monad
>
> import CFLP
> import CFLP.Control.Monad.Update
> import CFLP.Control.Strategy

We define an interface for choice stores that provide an operation to
lookup a previously made choice. The first argument of `assertChoice`
is a dummy argument to fix the type of the store in partial
applications.

> class ChoiceStore c
>  where
>   lookupChoice :: Int -> c -> Maybe Int
>   assertChoice :: MonadPlus m => c -> Int -> Int -> c -> m c

A finite map mapping unique identifiers to integers is a
`ChoiceStore`. The `assertChoice` operations fails to insert
conflicting choices.

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

The operation `labelChoices` takes a unique label and a list of
monadic values that can be constrained with choice constraints. The
result is a list of monadic actions that are constrained to take the
same alternative at every shared occurrence when collecting
constraints.

> labeledChoices :: (Monad m, ChoiceStore c, MonadUpdate c m)
>                => c -> Int -> [m a] -> [m a]
> labeledChoices c u xs =
>   maybe (zipWith constrain [(0::Int)..] xs)
>         ((:[]).(xs!!))
>         (lookupChoice u c)
>  where constrain n = (update (assertChoice c u n)>>)

If a choice with the same label has been created previously and the
label is already constrained to an alternative, then this alternative
is returned directly and no choice is created.

This situation occurs when a shared logic variable is renarrowed when
it is demanded again during a computation.


Transformer for Contexts and Strategies
---------------------------------------

We define a transformer for evaluation contexts that adds a choice
store.

> data StoreCTC c = StoreCTC ChoiceStoreIM c

A transformed store is itself a choice store and dispatches the calls
to the internal choice store.

> instance ChoiceStore (StoreCTC c)
>  where
>   lookupChoice n (StoreCTC c _) = lookupChoice n c
>   assertChoice _ n m (StoreCTC c s)
>     = liftM (`StoreCTC`s) (assertChoice c n m c)

The type constructor `StoreCTC` is an evaluation context transformer.

> instance Transformer StoreCTC
>  where
>   project (StoreCTC _ s) = s
>   replace (StoreCTC c _) = StoreCTC c

We define uniform liftings for choice stores: a choice store that is
transformed with an arbitrary transformer is still a choice store.

> instance (ChoiceStore c, Transformer t) => ChoiceStore (t c)
>  where
>   lookupChoice n     = lookupChoice n . project
>   assertChoice _ n m = inside (\c -> assertChoice c n m c)

We define a new type for strategies that ensure call-time choice
semantics.

> newtype CTC s a = CTC { fromCTC :: s a }
>  deriving (Monad, MonadPlus, Enumerable)
>
> type instance Ctx (CTC s) = StoreCTC (Ctx s)
> type instance Res (CTC s) = CTC (Res s)

The type `CTC` is a strategy transformer for strategies that have
acces to a choice store.

> instance ChoiceStore c => StrategyT c CTC
>  where
>   liftStrategy _ = CTC
>   baseStrategy _ = fromCTC
>
>   extendContext _ = StoreCTC noChoices
>   extendChoices   = labeledChoices
>
>   alterNarrowed c n isn
>     | isJust (lookupChoice n c) = return True
>     | otherwise = isn

Finally, we provide an instance for the type class `CFLP` that is a
shortcut for the class constraints od CFLP computations.

> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Monadic (UpdateT (StoreCTC ()) m)))
