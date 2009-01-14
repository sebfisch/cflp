% Monad Transformer for Updateable State and Delayed Computations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

We define a monad transformer that turns an arbitrary instance of
`MonadPlus` into a `MonadUpdate` and a `MonadDelay`. The challenge is
to implement the interface without threading a store through monadic
computations and shared monadic computations are evaluated only once.

> {-# LANGUAGE 
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       RankNTypes
>   #-}
>
> module Control.Monad.Trans.Update ( UpdateT ) where
>
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Trans
> import Control.Monad.Update

We define a monad transformer `UpdateT` that adds the capability of
non-deterministic state updates to arbitrary instances of
`MonadPlus`. Monadic actions in the resulting monads are data terms if
monadic actions are data terms in the base monad. As a consequence,
they are evaluated only once if they are shared.

> newtype UpdateT s m a = UpdateT { unUpdateT :: m (WithUpdate s m a) }
> data WithUpdate s m a
>   = Return a
>   | Update (forall m' . MonadPlus m' => s -> m' s) (UpdateT s m a)

The updating monadic action must be polymorphic in the used monad
`m'`.

> instance MonadPlus m => MonadUpdate s (UpdateT s m)
>  where
>   update upd = UpdateT (return (Update upd (return ())))

A transformed instance of `MonadPlus` is an instance of `MonadUpdate`.

> instance MonadPlus m => Update s (UpdateT s m) m
>  where
>   updateState = run
>    where
>     run :: MonadPlus m => UpdateT s m a -> StateT s m a
>     run x = lift (unUpdateT x) >>= doUpdate
>
>     doUpdate (Return a)     = return a
>     doUpdate (Update upd y) = do update upd; run y

It is also an instance of `Update` where results are returned in the
base monad. In order to perform stored updates, we thread a state
through the monadic computation.

> instance MonadPlus m => Update s (UpdateT s m) (UpdateT s m)
>  where
>   updateState = run
>    where
>     run :: MonadPlus m => UpdateT s m a -> StateT s (UpdateT s m) a
>     run x = lift (lift (unUpdateT x)) >>= doUpdate
>
>     doUpdate (Return a)     = return a
>     doUpdate (Update upd y) = do update upd; lift (update upd); run y

We define another instance of `Update` where results are not returned
in the base monad but in the transformed base monad. This instance is
useful to support computations that may or may not consider the
threaded store. All upcate actions are kept in the monadic values and
threaded additionally.

> instance Monad m => Monad (UpdateT s m)
>  where
>   return = UpdateT . return . Return
>
>   x >>= f = UpdateT (unUpdateT x >>= g)
>    where g (Return a)     = unUpdateT (f a)
>          g (Update upd y) = return (Update upd (y >>= f))
>
> instance MonadPlus m => MonadPlus (UpdateT s m)
>  where
>   mzero       = UpdateT mzero
>   x `mplus` y = UpdateT (unUpdateT x `mplus` unUpdateT y)
>
> instance MonadTrans (UpdateT s)
>  where
>   lift = UpdateT . liftM Return

We specify that a transformed monad is indeed a monad, that it is an
instance of `MonadPlus` if the base monad is, and that, `UpdateT`
(with an arbitrary store `s`) is a monad transformer.

> instance Show a => Show (UpdateT s [] a)
>  where
>   show (UpdateT x) = show x
>
> instance Show a => Show (WithUpdate cs [] a)
>  where
>   show (Return x) = "(Return "++show x++")"
>   show (Update _ (UpdateT x)) = "(Update _ "++show x++")"

To simplify debugging, we define `Show` instances for transformed list
monads.

