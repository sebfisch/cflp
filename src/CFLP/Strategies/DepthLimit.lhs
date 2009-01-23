% Depth Limiting for Non-Deterministic Computations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a strategy transformer that extends the
evaluation context with a limit for the search depth.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       TypeFamilies
>   #-}
>
> module CFLP.Strategies.DepthLimit (
>
>   DepthLimiter(..), DepthLim, DepthLimCtx, limitDepth, setDepthLimit
>
>  ) where
>
> import Control.Monad
>
> import CFLP.Control.Monad.Update
>
> import CFLP.Control.Strategy
>
> import CFLP.Strategies.DepthCounter

The interface of an evaluation context that can store a depth limit
is given by the following type class.

> class DepthLimiter c
>  where
>   depthLimit      :: c -> Int
>   resetDepthLimit :: c -> Int -> c -> c

We define uniform liftings for depth limiters over arbitrary context
transformers.

> instance (DepthLimiter c, Transformer t) => DepthLimiter (t c)
>  where
>   depthLimit = depthLimit . project
>
>   resetDepthLimit _ l c = replace c (resetDepthLimit undefined l (project c))

The operation `setDepthLimit` is used in computations to change the
depth limit.

> setDepthLimit :: (Monad s, DepthLimiter c, MonadUpdate c s)
>               => c -> Int -> s ()
> setDepthLimit c l = update (return . resetDepthLimit c l)

A depth limiting context adds a depth limit to the evaluation context.

> data DepthLimCtx c = DepthLimCtx Int c

It is an instance of `DepthLimiter`.

> instance DepthLimiter (DepthLimCtx c)
>  where
>   depthLimit (DepthLimCtx l _) = l
>
>   resetDepthLimit _ l (DepthLimCtx _ c) = DepthLimCtx l c

It also is a transformer for evaluation contexts

> instance Transformer DepthLimCtx
>  where
>   project (DepthLimCtx _ c) = c
>   replace (DepthLimCtx l _) = DepthLimCtx l

We define a strategy transformer for depth limiting.

> newtype DepthLim s a = DepthLim { fromDepthLim :: s a }
>  deriving (Monad, MonadPlus, Enumerable)
>
> type instance Ctx (DepthLim s) = DepthLimCtx (Ctx s)
> type instance Res (DepthLim s) = DepthLim (Res s)

The strategy-transformer instance increments the counter at each
non-deterministic choice and prunes the choices if the limit is
exceeded.

> instance (DepthCounter c, DepthLimiter c) => StrategyT c DepthLim
>  where
>   liftStrategy _ = DepthLim
>   baseStrategy _ = fromDepthLim
>
>   extendChoices c _ xs
>     | currentDepth c < depthLimit c
>       = map (update (return . incrementDepth c)>>) xs
>     | otherwise = []

The operation `limitDepth` adds a depth limit to a strategy.

> limitDepth :: Monad s => Int -> s c -> DepthLim s (DepthLimCtx c)
> limitDepth l = DepthLim . liftM (DepthLimCtx l)

