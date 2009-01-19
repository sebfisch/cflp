% Call-Time Choice as Strategy Transformer
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module implements call-time choice semantics of non-deterministic
programs as a strategy transformer.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies
>   #-}
>
> module Control.Strategy.Trans.CallTimeChoice where
>
> import Data.Maybe
>
> import Control.Monad
> import Control.Strategy
> import Control.Strategy.Trans
>
> import Control.Constraint.Choice
>
> import Control.CFLP

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

The type `CTC` is a strategy transformer.

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


> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Monadic (UpdateT (StoreCTC ()) m)))
