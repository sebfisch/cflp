% Monads with Non-Deterministically Updateable State
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

We define type classes and instances for monads that
non-deterministically update state. The challenge is to define the
interface such that instances can implement it without threading a
store through monadic computations and shared monadic computations are
evaluated only once.

> {-# LANGUAGE 
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       RankNTypes
>   #-}
>
> module Control.Monad.Update (
>
>   -- type classes
>   MonadUpdate(..), Update(..),
>
>   -- monad transformer
>   UpdateT
>
> ) where
> 
> import Control.Monad.State
> import Control.Monad.Trans
>
> class MonadPlus m => MonadUpdate s m
>  where
>   update :: (forall m' . MonadPlus m' => s -> m' s) -> m ()

A monad that supports non-deterministic state updates is an instance
of the class `MonadUpdate` that provides an operation to incorporate a
monadic update-action into monadic computations.

> instance MonadPlus m => MonadUpdate s (StateT s m)
>  where
>   update upd = get >>= upd >>= put

An instance of `MonadPlus` that threads a state can update that state
non-deterministically.

> class (MonadPlus m, MonadPlus m') => Update s m m'
>  where
>   updateState :: m a -> StateT s m' a

We also define an interface for monads that perform associated updates
in a state that is threaded through a (possibly, but not necessarily
different) monad.

We use the state monad transformer `StateT` to thread the constraint
store through the monad that returns the results.

> instance MonadPlus m => Update s (StateT s m) m
>  where
>   updateState = id

Again, a state threading monad gives rise to a natural instance, where
results are returned in the base monad.

State monads are a natural choice for a monad that updates state, but
they have a drawback: monadic values are functions that are reexecuted
for each shared occurrence of a monadic sub computation.

Shared Monadic Values
---------------------

We define a monad transformer `UpdateT` that adds the capability of
non-deterministic state updates to arbitrary instances of
`MonadPlus`. Monadic actions in the resulting monads are data terms if
monadic actions are data terms in the base monad. As a consequence,
they are evaluated only once if they are shared.

> newtype UpdateT s m a = UpdateT { unUpdateT :: m (WithUpdate s m a) }
> data WithUpdate s m a
>   = Return a
>   | Update (forall m' . MonadPlus m' => s -> m' s)
>            (UpdateT s m a)

The type `m'` of the updating monadic action is polymorphic.

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
>     doUpdate (Update upd y) = do lift (update upd); update upd; run y

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

