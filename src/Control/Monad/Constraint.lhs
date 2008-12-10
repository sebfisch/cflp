% Constraint Collecting Monads
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

We define type classes and instances for monads that can collect
constraints. The challenge is to define the interface such that
instances can implement it without threading a store through monadic
computations and shared monadic computations are evaluated only once.

> {-# LANGUAGE 
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       ExistentialQuantification
>   #-}
>
> module Control.Monad.Constraint (
>
>   -- type classes
>   ConstraintStore(..), MonadConstr(..), MonadSolve(..),
>
>   -- monad transformer
>   ConstrT
>
> ) where
> 
> import Control.Monad.State
> import Control.Monad.Trans
>
> class ConstraintStore c cs
>  where
>   assert :: (MonadState cs m, MonadPlus m) => c -> m ()

Constraint Stores provide an operation to assert a constraint into a
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

> class (MonadPlus m, MonadPlus m') => MonadSolve cs m m'
>  where
>   solve :: m a -> StateT cs m' a

We also define an interface for monads that can solve associated
constraints by threading a constraint store through a (possibly, but
not necessarily different) monad.

We use the state monad transformer `StateT` to thread the constraint
store through the monad that returns the results.

> instance MonadPlus m => MonadSolve cs (StateT cs m) m
>  where
>   solve = id

Again, a state threading monad gives rise to a natural instance, where
results are returned in the base monad.

State monads are a natural choice for a constraint monad, but they
have a drawback: monadic values are functions that are reexecuted for
each shared occurrence of a monadic sub computation.

Shared Monadic Values
---------------------

We define a monad transformer `ConstrT` that adds the capability of
collecting and solving constraints to arbitrary instances of
`MonadPlus`. Monadic actions in the resulting monads are data terms if
monadic actions are data terms in the base monad. As a consequence,
they are evaluated only once if they are shared.

> newtype ConstrT cs m a = ConstrT { unConstrT :: m (WithConstr cs m a) }
> data WithConstr cs m a
>   = Return a
>   | forall c . ConstraintStore c cs => Constr c (ConstrT cs m a)

The type `c` of collected constraints is existentially quantified in
order to allow different types of constraints in the same monadic
action. All types of constraints that are collected in a monadic
action need to be supported by the constraint store of type `cs`.

> instance (MonadPlus m, ConstraintStore c cs) => MonadConstr c (ConstrT cs m)
>  where
>   constr c = ConstrT (return (Constr c (return ())))

A transformed instance of `MonadPlus` is an instance of `MonadConstr`.

> instance MonadPlus m => MonadSolve cs (ConstrT cs m) m
>  where
>   solve = run
>    where
>     run :: MonadPlus m => ConstrT cs m a -> StateT cs m a
>     run x = lift (unConstrT x) >>= constrain
>
>     constrain (Return a)   = return a
>     constrain (Constr c y) = do constr c; run y

It is also an instance of `MonadSolve` where results are returned in
the base monad. In order to eliminate stored constraints, we thread a
constraint store through the monadic value and assert the associated
constraints into the store.

> instance MonadPlus m => MonadSolve cs (ConstrT cs m) (ConstrT cs m)
>  where
>   solve = run
>    where
>     run :: MonadPlus m => ConstrT cs m a -> StateT cs (ConstrT cs m) a
>     run x = lift (lift (unConstrT x)) >>= constrain
>
>     constrain (Return a)   = return a
>     constrain (Constr c y) = do lift (constr c); constr c; run y

We define another instance of `MonadSolve` where results are not
returned in the base monad but in the transformed base monad. This
instance is useful to support computations that may or may not
consider the threaded constraint store. All constraints are kept in
the monadic values and threaded additionally.

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

We specify that a transformed monad is indeed a monad, that it is an
instance of `MonadPlus` if the base monad is, and that, `ConstrT`
(with an arbitrary constraint store `cs`) is a monad transformer.

> instance Show a => Show (ConstrT cs [] a)
>  where
>   show (ConstrT x) = show x
>
> instance Show a => Show (WithConstr cs [] a)
>  where
>   show (Return x) = "(Return "++show x++")"
>   show (Constr _ (ConstrT x)) = "(Constr _ "++show x++")"

To simplify debugging, we define `Show` instances for transformed list
monads. Unfortunately, I don't know an easy way to show collected
constraints, because their type is not determined by the constraint
store and not mentioned in the signature of the instances.

