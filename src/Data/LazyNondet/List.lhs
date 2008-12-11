% Lazy Non-Deterministic Lists
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic lists.

> {-# LANGUAGE
>       FlexibleInstances
>   #-}
>
> module Data.LazyNondet.List where
>
> import Data.Data
> import Data.LazyNondet
> import Data.LazyNondet.Bool
>
> import Control.Monad.Constraint
>
> instance DataConstr [()] where dataConstr = toConstr
>
> nil :: Monad m => Nondet m [a]
> nil = cons ([] :: [()])
>
> dNil :: (cs -> Nondet m a) -> (ConIndex, cs -> Branch m a)
> dNil = decons ([] :: [()])
>
> infixr 5 ^:
> (^:) :: Monad m => Nondet m a -> Nondet m [a] -> Nondet m [a]
> (^:) = cons ((:) :: () -> [()] -> [()])
>
> dCons :: (cs -> Nondet m a -> Nondet m [a] -> Nondet m b)
>       -> (ConIndex, cs -> Branch m b)
> dCons = decons ((:) :: () -> [()] -> [()])
>
> fromList :: Monad m => [Nondet m a] -> Nondet m [a]
> fromList = foldr (^:) nil

We can use logic variables of a list type if there are logic variables
for the element type.

> instance Unknown a => Unknown [a]
>  where
>   unknown = withUnique $ \u1 u2 -> 
>              oneOf [nil, unknown u1 ^: unknown u2]

Some operations on lists:

> null :: MonadSolve cs m m => Nondet m [a] -> cs -> Nondet m Bool
> null xs = caseOf xs [dNil (\_ -> true), dCons (\_ _ _ -> false)]
>
> head :: MonadSolve cs m m => Nondet m [a] -> cs -> Nondet m a
> head l = caseOf l [dCons (\_ x _ -> x)]
>
> tail :: MonadSolve cs m m => Nondet m [a] -> cs -> Nondet m [a]
> tail l = caseOf l [dCons (\_ _ xs -> xs)]

