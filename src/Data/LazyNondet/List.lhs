% Lazy Non-Deterministic Lists
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic lists.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.List where
>
> import Data.Data
> import Data.LazyNondet
> import Data.LazyNondet.Bool
>
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> instance ConsRep [()] where consRep = toConstr
>
> nil :: Monad m => Nondet m [a]
> nil = cons ([] :: [()])
>
> pNil :: (cs -> Nondet m a) -> Match cs m a
> pNil = match ([] :: [()])
>
> infixr 5 ^:
> (^:) :: Monad m => Nondet m a -> Nondet m [a] -> Nondet m [a]
> (^:) = cons ((:) :: () -> [()] -> [()])
>
> pCons :: (cs -> Nondet m a -> Nondet m [a] -> Nondet m b) -> Match cs m b
> pCons = match ((:) :: () -> [()] -> [()])
>
> fromList :: Monad m => [Nondet m a] -> Nondet m [a]
> fromList = foldr (^:) nil

We can use logic variables of a list type if there are logic variables
for the element type.

> instance Narrow cs a => Narrow cs [a]
>  where
>   narrow cs = withUnique $ \u1 u2 -> 
>                 oneOf [nil, unknown cs u1 ^: unknown cs u2]

Some operations on lists:

> null :: (MonadSolve cs m m, MonadConstr Choice m, Narrow cs a)
>      => Nondet m [a] -> cs -> Nondet m Bool
> null xs = caseOf_ xs [pNil (\_ -> true)] false
>
> head :: (MonadSolve cs m m, MonadConstr Choice m, Narrow cs a)
>      => Nondet m [a] -> cs -> Nondet m a
> head l = caseOf l [pCons (\_ x _ -> x)]
>
> tail :: (MonadSolve cs m m, MonadConstr Choice m, Narrow cs a)
>      => Nondet m [a] -> cs -> Nondet m [a]
> tail l = caseOf l [pCons (\_ _ xs -> xs)]

