% Stragtegies for Constraint Functional-Logic Programs
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module implements interfaces for strategies and strategy
transformers.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       FunctionalDependencies,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeOperators,
>       TypeFamilies
>   #-}
>
> {-# OPTIONS_GHC
>       -fno-warn-unused-imports
>   #-}
>
> module Control.Strategy where
>
> import Control.Monad.State
> import Control.Monad.Update
> import Control.Monad.Trans.Update ( UpdateT ) -- here ghc warns spuriously

Results of a non-deterministic computation can be enumerated if the
strategy is an instance of the `Enumerable` class.

> class Enumerable s
>  where
>   enumeration :: s a -> [a]

A strategy provides an operation choose that is used for constructing
non-deterministic choices.

> type family Ctx (s :: * -> *)
> type family Res (s :: * -> *) :: * -> *
>
> type instance Res (UpdateT c m) = m
>
> class Strategy c s
>  where
>   emptyContext :: s c -> Ctx s
>   choose       :: c -> Int -> [s a] -> s a
>   isNarrowed   :: c -> Int -> s Bool 

Instances of the type class `MonadPlus` can be used as strategies that
ignore the evaluation context.

> newtype Monadic m a = Monadic { fromMonadic :: m a }
>  deriving (Monad, MonadPlus, Enumerable, MonadUpdate c)
>
> type instance Res (Monadic s) = Monadic (Res s)
> type instance Ctx (Monadic m) = ()
>
> instance MonadPlus m => Strategy c (Monadic m)
>  where
>   emptyContext _ = ()
>
>   choose _ _ [x] = x
>   choose _ _ xs  = foldr mplus mzero xs
>
>   isNarrowed _ _ = return False


The following instance provides the operation `updateState` for
monadic strategies.

> instance Update s m m' => Update s (Monadic m) (Monadic m')
>  where
>   updateState x = StateT (Monadic . runStateT (updateState (fromMonadic x)))


Transforming Evaluation Contexts
================================

Evaluation contexts can be extended by strategy transformers using
context transformers.

> class Transformer t
>  where
>   project :: t a -> a
>   replace :: t a -> a -> t a

The operation `inside` transforms the base context of a transformed
evaluation context with a monadic update operation.

> inside :: (Monad m, Transformer t) => (a -> m a) -> t a -> m (t a)
> inside f t = liftM (replace t) (f (project t))


