% Constraint Collecting Monads
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% November, 2008

We define type classes and instances for monads that can collect
constraints. The challenge is to define the interface such that
instances can implement it without threading a store through monadic
computations and shared monadic computations are evaluated only once.

> {-# OPTIONS 
>      -XMultiParamTypeClasses
>      -XFlexibleInstances
>      -XExistentialQuantification
>   #-}
>
> module Control.Monad.Constraint (
>
>   -- type classes
>   ConstraintStore(..), MonadConstr(..), RunConstr(..),
>
>   -- monad transformer
>   ConstrT
>
> ) where
> 
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Trans
>
> class ConstraintStore c cs
>  where
>   assert :: (MonadState cs m, MonadPlus m) => c -> m ()

Constraint Stores provides an operation to assert a constraint into a
store. The constraint store is manipulated in an instance of
`MonadState`. The `assert` operation may fail or branch depending on
the given constraint or the current store and is, hence, performed in
an instance of `MonadPlus`.

A constraint store may support different types of constraints and a
constraint may be supported by different constraint stores.

> class MonadPlus m => MonadConstr c m
>  where
>   constr :: c -> m ()

A monad that supports collecting constraints is an instance of the
class `MonadConstr` that provides an operation to associate a
constraint of type `c` to monadic computations. One monad may support
different types of constraints and the same constraint type may be
supported by different monads.

> instance (MonadPlus m, ConstraintStore c cs) => MonadConstr c (StateT cs m)
>  where
>   constr = assert

An instance of `MonadPlus` that threads a constraint store can be
constrained with constraints that are supported by the threaded store.

State monads are a natural choice for a constraint monad, but they
have a drawback: monadic values are functions that are reexecuted for
each shared occurrence of a monadic sub computation.

> newtype ConstrT cs m a = ConstrT { unConstrT :: m (WithConstr cs m a) }
> data WithConstr cs m a
>   = Return a
>   | forall c . ConstraintStore c cs => Constr c (ConstrT cs m a)


Monad Transformer
-----------------

We define a monad transformer `ConstrT` that adds the capability of
collecting constraints to arbitrary instances of `MonadPlus`. Monadic
actions in the resulting monads are data terms if monadic actions are
data terms in the base monad. As a consequence, they are evaluated
only once, even if they are shared.

The type `c` of collected constraints is existentially quantified in
order to allow different types of constraints in the same monadic
action. All types of constraints that are collected in a monadic
action need to be supported by the constraint store of type `cs`.

> runConstrT :: MonadPlus m => ConstrT cs m a -> StateT cs m a
> runConstrT = run
>  where
>   run :: MonadPlus m => ConstrT cs m a -> StateT cs m a
>   run x = lift (unConstrT x) >>= constrain
>
>   constrain (Return a)   = return a
>   constrain (Constr c y) = do constr c; run y

In order to eliminate stored constraints, we thread a constraint store
through the monadic value and assert the associated constraints into
the store.

We use the state monad transformer `StateT` to thread the constraint
store through the base monad of the constraint monad.

> instance (MonadPlus m, ConstraintStore c cs) => MonadConstr c (ConstrT cs m)
>  where
>   constr c = ConstrT (return (Constr c (return ())))

Transformed monads can collect constraints and are themselves monads.

> instance Monad m => Monad (ConstrT cs m)
>  where
>   return = ConstrT . return . Return
>
>   x >>= f = ConstrT (unConstrT x >>= g)
>    where g (Return a)   = unConstrT (f a)
>          g (Constr c y) = return (Constr c (y >>= f))
>
> instance MonadPlus m => MonadPlus (ConstrT cs m)
>  where
>   mzero       = ConstrT mzero
>   x `mplus` y = ConstrT (unConstrT x `mplus` unConstrT y)
>
> instance MonadTrans (ConstrT cs)
>  where
>   lift x = ConstrT (x >>= return . Return)

If the base monad is an instance of `MonadPlus`, then the transformed
monad also is. Finally, we specify that `ConstrT` (with an arbitrary
constraint store `cs`) is a monad transformer.

> class (MonadPlus m, MonadTrans (t cs)) => RunConstr cs m t
>  where
>   runConstr :: t cs m a -> StateT cs m a

We also define an interface for monads that can solve associated
constraints. Solutions may be returned in an arbitrary monad that
doesn't need to support constraints.

> instance MonadPlus m => RunConstr cs m StateT
>  where
>   runConstr = id
>
> instance MonadPlus m => RunConstr cs m ConstrT
>  where
>   runConstr = runConstrT

Both state and constraint monads can solve associated constraints.

