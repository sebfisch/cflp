% Randomization for CFL Computations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a strategy transformer that randomly reorders
choices in the search space.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       TypeFamilies
>   #-}
>
> module CFLP.Strategies.Random (
>
>   Randomiser(..), Rnd, RndCtx, randomise
>
>  ) where
>
> import Control.Monad
> import Control.Monad.Random
>
> import CFLP.Control.Monad.Update
>
> import CFLP.Control.Strategy

The interface of an evaluation context that can reorder choices
randomly is given by the following type class.

> class Randomiser c
>  where
>   getRandomGen :: c -> StdGen
>   setRandomGen :: c -> StdGen -> c -> c

The first argument of `setRandomGen` will always be ignored and is
only used to support the type checker.

We define uniform liftings for randomisers over arbitrary context
transformers.

> instance (Randomiser c, Transformer t) => Randomiser (t c)
>  where
>   getRandomGen = getRandomGen . project
>
>   setRandomGen _ r c = replace c (setRandomGen undefined r (project c))

A random context adds a counter for the depth.

> data RndCtx c = RndCtx StdGen c

It is an instance of `Randomiser`.

> instance Randomiser (RndCtx c)
>  where
>   getRandomGen     (RndCtx r _) = r
>   setRandomGen _ r (RndCtx _ c) = RndCtx r c

It also is a transformer for evaluation contexts

> instance Transformer RndCtx
>  where
>   project (RndCtx _ c) = c
>   replace (RndCtx d _) = RndCtx d

We define a strategy transformer for depth counting.

> newtype Rnd s a = Rnd { fromRnd :: s a }
>  deriving (Monad, MonadPlus, Enumerable)
>
> type instance Ctx (Rnd s) = RndCtx (Ctx s)
> type instance Res (Rnd s) = Rnd (Res s)

The strategy-transformer instance shuffles each non-deterministic
choice.

> instance Randomiser c => StrategyT c Rnd
>  where
>   liftStrategy _ = Rnd
>   baseStrategy _ = fromRnd
>
>   extendChoices c _ xs =
>     evalRand (shuffle xs >>= mapM (setRndGen c)) (getRandomGen c)
>
> shuffle :: MonadRandom rnd => [a] -> rnd [a]
> shuffle xs = shuffleWithLen (length xs) xs
>
> shuffleWithLen :: MonadRandom rnd => Int -> [a] -> rnd [a]
> shuffleWithLen 0   _  = return []
> shuffleWithLen len xs = do
>   let len_1 = len-1
>   n <- getRandomR (0,len_1)
>   let (ys,z:zs) = splitAt n xs
>   liftM (z:) (shuffleWithLen len_1 (ys++zs))
>
> setRndGen :: (Randomiser c, Monad m, MonadUpdate c m)
>           => c -> m a -> Rand StdGen (m a)
> setRndGen c x = do
>   r <- getSplit
>   return (update (return . setRandomGen c r) >> x)

The operation `random` adds randomisation to a strategy.

> randomise :: Monad s => s c -> Rnd s (RndCtx c)
> randomise = Rnd . liftM (RndCtx (mkStdGen 42))


