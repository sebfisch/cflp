% Higher-Order Non-Deterministic Operations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines combinators for higher-order CFLP.

> {-# LANGUAGE 
>       MultiParamTypeClasses, NoMonomorphismRestriction,
>       FunctionalDependencies,
>       TypeSynonymInstances,
>       UndecidableInstances,
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

> fun :: (Monad m, LiftFun f g, NestLambda g cs m t)
>     => f -> Nondet cs m t
> fun = nestLambda . liftFun

Here are private type classes that are used to implement `fun`.

> newtype Lifted cs m a b
>   = Lifted { lifted :: Nondet cs m a -> Context cs -> ID -> Nondet cs m b }

> class NestLambda a cs m b | a -> cs, a -> m, a -> b
>  where
>   nestLambda :: Monad m => a -> Nondet cs m b

Single-argument functions can be lifted using `lambda`.

> instance NestLambda (Lifted cs m a b) cs m (a -> b)
>  where
>   nestLambda = lambda . lifted

If we have a function on non-deterministic data we can lift it to the
`Nondet` type with the following instance.

> instance NestLambda f cs m b => NestLambda (Nondet cs m a -> f) cs m (a -> b)
>  where
>   nestLambda f = lambda (\x _ _ -> nestLambda (f x))

We provide a combinator `liftFun` for 

  * constructor functions that do not take a constraint store or a
    unique id,

  * deterministic functions that only take a constraint store, and

  * non-deterministic functions that only take a unique id.

> class LiftFun f g | f -> g
>  where
>   liftFun :: f -> g
>
> instance LiftFun (Nondet cs m a -> Nondet cs m b) (Lifted cs m a b)
>  where
>   liftFun f = Lifted (\x _ _ -> f x)
>
> instance LiftFun (Nondet cs m a -> Context cs -> Nondet cs m b)
>                  (Lifted cs m a b)
>  where
>   liftFun f = Lifted (\x cs _ -> f x cs)
>
> instance LiftFun (Nondet cs m a -> ID -> Nondet cs m b) (Lifted cs m a b)
>  where
>   liftFun f = Lifted (\x _ u -> f x u)
>
> instance LiftFun (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>                  (Lifted cs m a b)
>  where
>   liftFun = Lifted
>
> instance LiftFun (Nondet cs m b -> f) g => 
>          LiftFun (Nondet cs m a -> Nondet cs m b -> f) (Nondet cs m a -> g)
>  where
>   liftFun f = liftFun . f
