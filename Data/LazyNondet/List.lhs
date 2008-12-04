% Lazy Non-Deterministic Lists
% [Sebastian Fischer](mailto:sebf@informatik.uni-kiel.de)
% November, 2008

This module provides non-deterministic lists.

> module Data.LazyNondet.List where
>
> import Data.Data
> import Data.LazyNondet
>
> nil :: Monad m => Typed m [a]
> nil = Typed (return (cons (toConstr ([]::[()])) []))
>
> (^:) :: Monad m => Typed m a -> Typed m [a] -> Typed m [a]
> x^:xs = Typed (return (cons (toConstr [()]) [untyped x, untyped xs]))
>
> fromList :: Monad m => [Typed m a] -> Typed m [a]
> fromList = foldr (^:) nil

We can use logic variables of a list type if there are logic variables
for the element type.

> instance Unknown a => Unknown [a]
>  where
>   unknown = call (\u1 u2 -> oneOf [nil, unknown u1 ^: unknown u2])

