% Depth Monitoring for Non-Deterministic Computations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a strategy transformer that extends the
evaluation context with a counter for the search depth.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       TypeFamilies
>   #-}
>
> module CFLP.Strategies.DepthCounter (
>
>   DepthCounter(..), Depth, DepthCtx, countDepth
>
>  ) where
>
> import Control.Monad
>
> import CFLP.Control.Monad.Update
>
> import CFLP.Control.Strategy

The interface of an evaluation context that can store a depth counter
is given by the following type class.

> class DepthCounter c
>  where
>   currentDepth   :: c -> Int
>   incrementDepth :: c -> c -> c

The first argument of `incrementDepth` will always be ignored and is
only used to support the type checker.

We define uniform liftings for depth counters over arbitrary context
transformers.

> instance (DepthCounter c, Transformer t) => DepthCounter (t c)
>  where
>   currentDepth = currentDepth . project
>
>   incrementDepth _ c = replace c (incrementDepth undefined (project c))

A depth context adds a counter for the depth.

> data DepthCtx c = DepthCtx Int c

It is an instance of `DepthCounter`.

> instance DepthCounter (DepthCtx c)
>  where
>   currentDepth     (DepthCtx d _) = d
>   incrementDepth _ (DepthCtx d c) = DepthCtx (d+1) c

It also is a transformer for evaluation contexts

> instance Transformer DepthCtx
>  where
>   project (DepthCtx _ c) = c
>   replace (DepthCtx d _) = DepthCtx d

We define a strategy transformer for depth counting.

> newtype Depth s a = Depth { fromDepth :: s a }
>  deriving (Monad, MonadPlus, Enumerable)
>
> type instance Ctx (Depth s) = DepthCtx (Ctx s)
> type instance Res (Depth s) = Depth (Res s)

The operation `countDepth` the `Depth` constructor.

> countDepth :: s a -> Depth s a
> countDepth = Depth

The strategy-transformer instance increments the counter at each
non-deterministic choice.

> instance DepthCounter c => StrategyT c Depth
>  where
>   liftStrategy _ = Depth
>   baseStrategy _ = fromDepth
>
>   extendContext _ = DepthCtx 0
>
>   extendChoices c _ = map (update (return . incrementDepth c)>>)
