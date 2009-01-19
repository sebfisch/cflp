% Strategy Transformers
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module implements strategy transformers and uniform liftings for
some type classes.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       IncoherentInstances,
>       FlexibleInstances,
>       RankNTypes
>   #-}
>
> module Control.Strategy.Trans where
>
> import Control.Monad.State
> import Control.Monad.Update
> import Control.Strategy

A strategy transformer has operations to convert between the
transformed and the base strategy as well as operations to extend
evaluation contexts and lists of non-deterministic choices.

> class StrategyT c t
>  where
>   liftStrategy  :: c -> s a -> t s a
>   baseStrategy  :: c -> t s a -> s a
>
>   extendContext :: t s c -> Ctx s -> Ctx (t s)
>
>   extendChoices :: (Monad s, MonadUpdate c s)
>                 => c -> Int -> [t s a] -> [t s a]
>   extendChoices _ _ = id
>
>   alterNarrowed :: Monad s => c -> Int -> t s Bool -> t s Bool
>   alterNarrowed _ _ = id

A strategy can be transformed by a strategy transformer to another
strategy.

> instance (Monad s, MonadUpdate c s, Strategy c s, StrategyT c t)
>       => Strategy c (t s)
>  where
>   emptyContext c = extendContext c (emptyContext (undefined `forBaseOf` c))
>
>   choose c n = liftStrategy c
>              . choose c n
>              . map (baseStrategy c)
>              . extendChoices c n
>
>   isNarrowed c n = alterNarrowed c n (liftStrategy c (isNarrowed c n))
>
> forBaseOf :: s a -> t s a -> s a
> forBaseOf = const

Strategies remain updateable when transformed.

> instance (MonadUpdate c s, StrategyT c t) => MonadUpdate c (t s)
>  where
>   update upd = liftStrategy (undefined `forContextOf` upd) (update upd)
>
> forContextOf :: c -> (forall m . MonadPlus m => c -> m c) -> c
> forContextOf = const

They also provide an operation to update threaded state.

> instance (Update c s s', StrategyT c t) => Update c (t s) (t s')
>  where
>   updateState x
>    = let y = StateT (liftStrategy (undefined `forStateOf` y) .
>                      runStateT (updateState
>                                 (baseStrategy (undefined `forStateOf` y) x)))
>       in y
>
> forStateOf :: c -> StateT c m a -> c
> forStateOf = const

