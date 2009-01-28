% Stragtegies for Constraint Functional-Logic Programs
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module implements interfaces for strategies and strategy
transformers.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       FunctionalDependencies,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       IncoherentInstances,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeOperators,
>       TypeFamilies,
>       RankNTypes
>   #-}
>
> module CFLP.Control.Strategy (
>
>   Enumerable(..), Solvable(..), Ctx, Res, 
>
>   Strategy(..), Transformer(..), StrategyT(..),
>
>   Monadic(..), inside
>
>  ) where
>
> import Control.Monad.State
>
> import CFLP.Control.Monad.Update

Results of a non-deterministic computation can be enumerated if the
strategy is an instance of the `Enumerable` class.

> class Enumerable s
>  where
>   enumeration :: s a -> [a]

A strategy provides an operation choose that is used for constructing
non-deterministic choices.

We provide the following type families used when defining strategies:

  * `Ctx s` specifies the evaluation context of a strategy. Strategy
    transformer can extend the evaluation context later.

  * `Res s` specifies the monad in which results are returned by
    normal-form computations.

> type family Ctx (s :: * -> *)
> type family Res (s :: * -> *) :: * -> *

If we use the monad transformer `UpdateT` to add updateable state to a
monad, then the base monad is used to return results when computing
normal forms.

> type instance Res (UpdateT c m) = m

Evaluation context must provide a predicate that tells whether they
are solvable.

> class Solvable c
>  where
>   solvable     :: c -> Bool
>   bindVars :: MonadPlus m => c -> m c

The unit context is solvable.

> instance Solvable ()
>  where
>   solvable _ = True
>   bindVars   = return

A strategy is parameterised by an evlauation context of type `c`. The
type of this context may be different from `Ctx s` because a strategy
can be transformed. The strategy operations need to be able to access
the final evaluation context after applying all transformations that
may extend the context.

A value of type `s a` represents a CFLP computation that yields a
value of type `a` where the strategy `s` is used for evaluation.

> class Strategy c s where

Strategies provide the following operations:

>   choose :: c -> Int -> [s a] -> s a

is used to cconstruct non-deterministic choices of computations. We
pass an evaluation context of type `c` and a unique label of type
`Int` that identifies the constructed choice.

>   isNarrowed :: c -> Int -> s Bool

specifies whether a choice identified by the given label of type `Int`
is already narrowed w.r.t. the given evaluation context of type
`c`. The result is returned as computation of type `s Bool` rather
than only `Bool`, again, to support the type checker occasionally.

A Default Instance
------------------

Usually, strategies are instances of `MonadPlus`. In fact we can wrap
every instance of `MonadPlus` to make it an instance of `Strategy` for
arbitrary evaluation contexts `c` (that are ignored).

> newtype Monadic m a = Monadic { fromMonadic :: m a }
>  deriving (Monad, MonadPlus, Enumerable, MonadUpdate c)

We use generalized newtype deriving to lift some type-class instances
over the newtype constructor.

The type instances for `Ctx` and `Res` are given as follows:

> type instance Ctx (Monadic m) = ()
> type instance Res (Monadic s) = Monadic (Res s)

Implementing the strategy operations with `MonadPlus` instances is
straigh-forward.

> instance MonadPlus m => Strategy c (Monadic m) where

The operation

>   choose _ _ xs = foldr1 mplus (mzero:xs)

uses `mplus` and `mzero` to construct the choice. Note that these are
the automatically derived operations.

>   isNarrowed _ _ = return False

always returns `False` because we ignore evaluation contexts here.

As we cannot derive an instance for the class `Update` automatically
(the newtype occurs twice in the instance head), we need to define the
lifting manually.

> instance Update s m m' => Update s (Monadic m) (Monadic m')
>  where
>   updateState x = StateT (Monadic . runStateT (updateState (fromMonadic x)))


Transforming Evaluation Contexts and Strategies
===============================================

Evaluation contexts can be extended by strategy transformers using
context transformers that are an instance of the class `Transformer`.

> class Transformer t where

This class provides operations

>   project :: t a -> a

to get the transformed value, and

>   replace :: t a -> a -> t a

to replace the wrapped value with a different one.

The operation

> inside :: (Monad m, Transformer t) => (a -> m a) -> t a -> m (t a)
> inside f t = liftM (replace t) (f (project t))

transforms the base value of a transformed value with a monadic update
operation.

If an evaluation context is solvable, then a transformed context also
is. This instance may overlap with more specific instances that
redefine the operation for specific solvers.

> instance (Solvable c, Transformer t) => Solvable (t c)
>  where
>   solvable = solvable . project
>   bindVars = inside bindVars


Strategy Transformers
---------------------

A strategy transformer is used to add functionality to
strategies. Transformers are parameterised by an evaluation context
just like strategies. 

If `t` is the type of a strategy transformer and `s` the type of a
strategy, then a value of type `t s a` represents a computation that
yields a value of type `a` using the strategy `s` transformed by `t`.

> class StrategyT c t where

Strategy transformers provide the following operations:

>   liftStrategy :: c -> s a -> t s a

lifts a computation using the base strategy to one that uses the
transformed strategy. The parameter of type `c` is only used to help
the type checker. It must be safe to pass `undefined` here.

>   baseStrategy  :: c -> t s a -> s a

takes a computation that uses the transformed strategy and yields one
that uses the base strategy. The first parameter is used to support
type checking and must be ignored.

>   extendChoices :: (Monad s, MonadUpdate c s)
>                 => c -> Int -> [t s a] -> [t s a]
>   extendChoices _ _ = id

can be used to update the evaluation context of the alternatives of
non-deterministic choices. We provide a default implementation for
instances of `StrategyT` that do not want to alter choices.

>   alterNarrowed :: Monad s => c -> Int -> t s Bool -> t s Bool
>   alterNarrowed _ _ = id

can be used to alter the predicate that determines whether the choice
identified by the given label is narrowed w.r.t. the given
context. The result of the original strategy is passed as an
additional argument. We provide a default implementation for instances
that do not want to alter this predicate.

If we have a strategy transformer and a strategy that is an updateable
monad, then the transformed strategy is again a strategy.

> instance (Monad s, MonadUpdate c s, Strategy c s, StrategyT c t)
>       => Strategy c (t s)
>  where

The operation `choose` extends the choices according to the
transformer and calls the `choose` operation of the base strategy with
the resulting choices.

>   choose c n = liftStrategy c
>              . choose c n
>              . map (baseStrategy c)
>              . extendChoices c n

The predicate `isNarrowed` is altered according to the strategy
transformer.

>   isNarrowed c n = alterNarrowed c n (liftStrategy c (isNarrowed c n))


Uniform Liftings
----------------

We can define instances for the type classes `MonadUpdate` and
`Update` for strategies that are transformed with arbitrary strategy
transformers.

The instances simply use the lifting functions where appropriate and
use type-constrained `const` functions where necessary.

> instance (MonadUpdate c s, StrategyT c t) => MonadUpdate c (t s)
>  where
>   update upd = liftStrategy (undefined `forContextOf` upd) (update upd)
>
> forContextOf :: c -> (forall m . MonadPlus m => c -> m c) -> c
> forContextOf = const
>
> instance (Update c s s', StrategyT c t) => Update c (t s) (t s')
>  where
>   updateState x
>    = let y = StateT (liftStrategy (undefined `forStateOf` y) .
>                      runStateT (updateState
>                                 (baseStrategy (undefined `forStateOf` y) x)))
>       in y
>
> forStateOf :: c -> StateT c m a -> c
> forStateOf = const

