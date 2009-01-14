% Monads with Non-Deterministically Updateable State
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

We define type classes and instances for monads that
non-deterministically update state.

> {-# LANGUAGE 
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       RankNTypes
>   #-}
>
> module Control.Monad.Update (
>
>   MonadUpdate(..), Update(..),
>
> ) where
> 
> import Control.Monad.State
>
> class MonadPlus m => MonadUpdate s m
>  where
>   update :: (forall m' . MonadPlus m' => s -> m' s) -> m ()

A monad that supports non-deterministic state updates is an instance
of the class `MonadUpdate` that defines an operation to incorporate a
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
