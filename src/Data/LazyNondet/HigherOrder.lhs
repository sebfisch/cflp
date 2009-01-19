% Higher-Order Non-Deterministic Operations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines combinators for higher-order CFLP.

> {-# LANGUAGE 
>       TypeFamilies,
>       FlexibleInstances,
>       FlexibleContexts,
>       MultiParamTypeClasses,
>       FunctionalDependencies,
>       UndecidableInstances
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

> apply :: (Monad m, Update cs m m)
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

> fun :: (Monad m, LiftFun f, NestLambda cs m t (Lift f))
>     => f -> Nondet cs m t
> fun = nestLambda . liftFun

Here are private type classes that are used to implement `fun`.

> class NestLambda cs m t a | a -> cs, a -> m, a -> t
>  where
>   nestLambda :: Monad m => a -> Nondet cs m t

Single-argument functions can be lifted using `lambda`.

> instance NestLambda cs m (a -> b)
>            (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>  where
>   nestLambda = lambda

If we have a function on non-deterministic data we can lift it to the
`Nondet` type with the following instance.

> instance NestLambda cs m t (Nondet cs m b -> f)
>       => NestLambda cs m (a -> t) (Nondet cs m a -> Nondet cs m b -> f)
>  where
>   nestLambda f = lambda (\x _ _ -> nestLambda (f x))

We'd prefer to use type families instead of fundeps (to get rif of the
undecidable instances pragma) but the following instance causes very
long type checking -- probably because of incompletely handled
super-class equalities in the current version of GHC:

~~~
instance (NestLambda (Nondet cs m b -> f),
          C (Nondet cs m b -> f) ~ cs, M  (Nondet cs m b -> f) ~ m)
      => NestLambda (Nondet cs m a -> Nondet cs m b -> f)
 where
  type C (Nondet cs m a -> Nondet cs m b -> f) = cs
  type M (Nondet cs m a -> Nondet cs m b -> f) = m
  type T (Nondet cs m a -> Nondet cs m b -> f) = a -> T (Nondet cs m b -> f)

  nestLambda f = lambda (\x _ _ -> nestLambda (f x))
~~~

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
>   type Lift (Nondet cs m a -> Nondet cs m b)
>     = Nondet cs m a -> Context cs -> ID -> Nondet cs m b
>
>   liftFun f x _ _ = f x
>
> instance LiftFun (Nondet cs m a -> Context cs -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> Context cs -> Nondet cs m b)
>     = Nondet cs m a -> Context cs -> ID -> Nondet cs m b
>
>   liftFun f x cs _ = f x cs
>
> instance LiftFun (Nondet cs m a -> ID -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> ID -> Nondet cs m b)
>     = Nondet cs m a -> Context cs -> ID -> Nondet cs m b
>
>   liftFun f x _ = f x
>
> instance LiftFun (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>  where
>   type Lift (Nondet cs m a -> Context cs -> ID -> Nondet cs m b)
>     = Nondet cs m a -> Context cs -> ID -> Nondet cs m b
>
>   liftFun = id
>
> instance LiftFun (Nondet cs m b -> f)
>       => LiftFun (Nondet cs m a -> Nondet cs m b -> f)
>  where
>   type Lift (Nondet cs m a -> Nondet cs m b -> f)
>     = Nondet cs m a -> Lift (Nondet cs m b -> f)
>
>   liftFun f = liftFun . f
