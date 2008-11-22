% Constraint Collecting Monads
% [Sebastian Fischer](mailto:sebf@informatik.uni-kiel.de)
% November, 2008

We define type classes and instances for monads that can collect
constraints. The challenge is to define the interface such that
instances can implement it without threading a store through monadic
computations and shared monadic computations are evaluated only once.

~~~ { .literatehaskell }

> {-# OPTIONS 
>      -XMultiParamTypeClasses
>      -XFlexibleInstances
>      -XExistentialQuantification
>   #-}
>
> module Control.Monad.Constraint (
>
>   -- type classes
>   ConstraintStore(..), Collect(..), 
>
>   -- monad transformer
>   CollectT, 
>
>   -- constraint solving
>   solution
>
> ) where
> 
> import Control.Monad
> import Control.Monad.Trans
> import Control.Monad.State
>
> class ConstraintStore c cs
>  where
>   assert :: (MonadState cs m, MonadPlus m) => c -> m ()

~~~

Constraint Stores provide an operation to assert a constraint. The
constraint store is manipulated in an instance of `MonadState`. The
`assert` operation may fail or branch depending on the given
constraint or the current store and, hence, returns the modified store
in an instance of `MonadPlus`.

A constraint store may support different types of constraints and a
constraint may be supported by different constraint stores.

~~~ { .literatehaskell }

> class Collect c m
>  where
>   collect :: c -> m ()

~~~

A monad that supports collecting constraints is an instance of the
class `Collect` that provides an operation to collect items of type
`c`. One monad may collect items of different types and the same item
may be collectable in different monads.

~~~ { .literatehaskell }

> newtype CollectT cs m a = CollectT { runCollectT :: m (WithCollect cs m a) }
> data WithCollect cs m a
>   = Lifted a
>   | forall c . ConstraintStore c cs => Collect c (CollectT cs m a)

~~~

We define a monad transformer `CollectT` that adds the capability of
collecting constraints to arbitrary monads. Monadic actions in the
resulting monads are data terms if monadic actions are data terms in
the base monad. As a consequence, they are evaluated only once, even
if they are shared.

The type `c` of collected constraints is existentially quantified in
order to allow different types of constraints in the same monadic
action. All types of constraints that are collected in a monadic action
need to be supported by the constraint store of type `cs`.

~~~ { .literatehaskell }

> instance (Monad m, ConstraintStore c cs) => Collect c (CollectT cs m)
>  where
>   collect c = CollectT (return (Collect c (return ())))

~~~

Transformed monads can collect constraints and are themselves monads.

~~~ { .literatehaskell }

> instance Monad m => Monad (CollectT cs m)
>  where
>   return = CollectT . return . Lifted
>
>   x >>= f = CollectT (runCollectT x >>= g)
>    where g (Lifted a)    = runCollectT (f a)
>          g (Collect c y) = return (Collect c (y >>= f))
>
> instance MonadPlus m => MonadPlus (CollectT cs m)
>  where
>   mzero       = CollectT mzero
>   x `mplus` y = CollectT (runCollectT x `mplus` runCollectT y)
>
> instance MonadTrans (CollectT cs)
>  where
>   lift x = CollectT (x >>= return . Lifted)

~~~

If the base monad is an instance of `MonadPlus`, then the transformed
monad also is. Finally, we specify that `CollectT` (with an arbitrary
constraint store `cs`) is a monad transformer.

~~~ { .literatehaskell }

> solution :: MonadPlus m => CollectT cs m a -> cs -> m (a,cs)
> solution = runStateT . solver
>  where
>   solver :: MonadPlus m => CollectT cs m a -> StateT cs m a
>   solver x = lift (runCollectT x) >>= solve
>
>   solve (Lifted a)    = return a
>   solve (Collect c y) = do assert c; solver y
>

~~~

In order to solve constraints, we thread a constraint store through
the monadic value, eliminate all occurrences of the constructor
`Collect`, and assert the associated constraints into the store.

