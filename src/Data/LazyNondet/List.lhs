% Lazy Non-Deterministic Lists
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic lists.

> module Data.LazyNondet.List where
>
> import Data.Data
> import Data.LazyNondet
> import Data.LazyNondet.Bool
>
> import Control.Monad.Constraint
>
> nil :: Monad m => Nondet m [a]
> nil = Typed (return (mkHNF (toConstr ([]::[()])) []))
>
> infixr 5 ^:
> (^:) :: Monad m => Nondet m a -> Nondet m [a] -> Nondet m [a]
> x^:xs = Typed (return (mkHNF (toConstr [()]) [untyped x, untyped xs]))
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
> null xs =
>   caseOf xs $ \xs' _ ->
>   case xs' of
>     Cons _ 1 _ -> true
>     _ -> false
>
> head :: MonadSolve cs m m => Nondet m [a] -> cs -> Nondet m a
> head l =
>   caseOf l $ \l' cs ->
>   case l' of
>     Cons _ 1 _ -> failure
>     Cons _ 2 [x',_] -> Typed x'
>
> tail :: MonadSolve cs m m => Nondet m [a] -> cs -> Nondet m [a]
> tail l =
>   caseOf l $ \l' cs ->
>   case l' of
>     Cons _ 1 _ -> failure
>     Cons _ 2 [_,xs'] -> Typed xs'
