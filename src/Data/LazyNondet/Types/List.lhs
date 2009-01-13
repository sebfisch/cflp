% Lazy Non-Deterministic Lists
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic lists.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.Types.List where
>
> import Data.Data
> import Data.LazyNondet
> import Data.LazyNondet.Types.Bool
>
> import Control.Monad.Update
>
> import Control.Constraint.Choice
>
> import Prelude hiding ( map, foldr )
> import qualified Prelude as P
>
> instance ConsRep [()] where consRep = toConstr
>
> nil :: Monad m => Nondet cs m [a]
> nil = cons ([] :: [()])
>
> pNil :: (Context cs -> Nondet cs m b) -> Match [a] cs m b
> pNil = match ([] :: [()])
>
> infixr 5 ^:
> (^:) :: Monad m => Nondet cs m a -> Nondet cs m [a] -> Nondet cs m [a]
> (^:) = cons ((:) :: () -> [()] -> [()])
>
> pCons :: (Context cs -> Nondet cs m a -> Nondet cs m [a] -> Nondet cs m b)
>       -> Match [a] cs m b
> pCons = match ((:) :: () -> [()] -> [()])
>
> fromList :: Monad m => [Nondet cs m a] -> Nondet cs m [a]
> fromList = P.foldr (^:) nil

We can use logic variables of a list type if there are logic variables
for the element type.

> instance (ChoiceStore cs, Narrow cs a) => Narrow cs [a]
>  where
>   narrow cs u = withUnique (\u1 u2 -> 
>                   (oneOf [nil, unknown u1 ^: unknown u2] cs u)) u

Some operations on lists:

> null :: Update cs m m => Nondet cs m [a] -> Context cs -> Nondet cs m Bool
> null xs = caseOf_ xs [pNil (const true)] false
>
> head :: Update cs m m => Nondet cs m [a] -> Context cs -> Nondet cs m a
> head l = caseOf l [pCons (\_ x _ -> x)]
>
> tail :: Update cs m m => Nondet cs m [a] -> Context cs -> Nondet cs m [a]
> tail l = caseOf l [pCons (\_ _ xs -> xs)]

Higher-order functions:

> map :: Update cs m m
>     => Nondet cs m (a -> b) -> Nondet cs m [a]
>     -> Context cs -> ID -> Nondet cs m [b]
> map f l cs = withUnique $ \u ->
>               foldr (fun (\x xs -> apply f x cs u ^: xs)) nil l cs
>
> foldr :: Update cs m m
>       => Nondet cs m (a -> b -> b) -> Nondet cs m b -> Nondet cs m [a]
>       -> Context cs -> ID -> Nondet cs m b
> foldr f y l cs = withUnique $ \u1 u2 u3 ->
>   caseOf l
>     [ pNil (const y)
>     , pCons (\cs x xs -> apply (apply f x cs u1) (foldr f y xs cs u2) cs u3)
>     ] cs

