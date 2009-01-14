% Higher-Order Non-Deterministic Operations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines combinators for higher-order CFLP.

> {-# LANGUAGE 
>       TypeFamilies,
>       FlexibleInstances,
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.HigherOrder (
>
>   fun, apply
>
> ) where
>
> import Data.LazyNondet.Types
> import Data.LazyNondet.Matching ( withHNF )
>
> import Control.Monad.Update

With the `lambda` combinator functions on non-deterministic data are
lifted to the `Nondet` type.

> lambda :: Monad m
>        => (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>        -> Nondet cs m (a -> b)
> lambda f = Typed . return $ Lambda (\x cs -> untyped . f (Typed x) cs)

To apply a lambda, we provide the combinator `apply`.

> apply :: Update cs m m
>       => Nondet cs m (a -> b) -> Nondet cs m a
>       -> Context cs -> ID -> Nondet cs m b
> apply f x cs u = withHNF f (\f cs ->
>   case f of
>     Lambda f -> Typed (f (untyped x) cs u)
>     FreeVar _ f -> apply (Typed f) x cs u
>     _ -> error "Data.LazyNondet.HigherOrder: cannot apply") cs

The overloaded operation `fun` converts a function on
non-deterministic data (of arbitrary arity) into a (possibly nested)
lambda.

> fun :: (Monad m, LiftFun f, NestLambda g, g ~ Lift f, m~M g, cs~C g, t~T g)
>     => f -> Nondet cs m t
> fun = nestLambda . liftFun

Here are private type classes that are used to implement `fun`.

> newtype Lifted cs m a b
>   = Lifted { lifted :: Nondet cs m a -> Context cs -> ID -> Nondet cs m b }

> class NestLambda a
>  where
>   type C a :: *
>   type M a :: * -> *
>   type T a :: *
>
>   nestLambda :: Monad (M a) => a -> Nondet (C a) (M a) (T a)

Single-argument functions can be lifted using `lambda`.

> instance NestLambda (Lifted cs m a b)
>  where
>   type C (Lifted cs m a b) = cs
>   type M (Lifted cs m a b) = m
>   type T (Lifted cs m a b) = a -> b
>
>   nestLambda = lambda . lifted

If we have a function on non-deterministic data we can lift it to the
`Nondet` type with the following instance.

> instance (NestLambda f, C f ~ cs, M f ~ m) => NestLambda (Nondet cs m a -> f)
>  where
>   type C (Nondet cs m a -> f) = cs
>   type M (Nondet cs m a -> f) = m
>   type T (Nondet cs m a -> f) = a -> T f
>
>   nestLambda f = lambda (\x _ _ -> nestLambda (f x))

We provide a combinator `liftFun` for 

  * constructor functions that do not take a constraint store or a
    unique id,

  * deterministic functions that only take a constraint store, and

  * non-deterministic functions that only take a unique id.

> class LiftFun f
>  where
>   type Lift f
>
>   liftFun :: f -> Lift f
>
> instance LiftFun (Nondet cs m a -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> Nondet cs m b) = Lifted cs m a b
>
>   liftFun f = Lifted (\x _ _ -> f x)
>
> instance LiftFun (Nondet cs m a -> Context cs -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> Context cs -> Nondet cs m b) = Lifted cs m a b
>
>   liftFun f = Lifted (\x cs _ -> f x cs)
>
> instance LiftFun (Nondet cs m a -> ID -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> ID -> Nondet cs m b) = Lifted cs m a b
>
>   liftFun f = Lifted (\x _ u -> f x u)
>
> instance LiftFun (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>           = Lifted cs m a b
>
>   liftFun = Lifted
>
> instance LiftFun (Nondet cs m b -> f)
>       => LiftFun (Nondet cs m a -> Nondet cs m b -> f)
>  where
>   type Lift (Nondet cs m a -> Nondet cs m b -> f)
>           = Nondet cs m a -> Lift (Nondet cs m b -> f)
>
>   liftFun f = liftFun . f
