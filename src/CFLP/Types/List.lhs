% Lazy Non-Deterministic Lists
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides non-deterministic lists.

> {-# LANGUAGE
>       NoMonomorphismRestriction,
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       NoMonoPatBinds,
>       TypeFamilies
>   #-}
>
> module CFLP.Types.List where
>
> import CFLP
> import CFLP.Types.Bool
>
> import Prelude hiding ( map, foldr )
> import qualified Prelude as P
>
> instance ApplyCons [a] where type Result [a] = [a]; applyCons = const
>
> instance Generic a => Generic [a]
>  where constr = cons "[]" [] dNil ! cons "(:)" (:) dCons
>
> dNil :: Decons [a]
> dNil c [] = Just (c [])
> dNil _ _  = Nothing
>
> dCons :: Generic a => Decons [a]
> dCons c (x:xs) = Just (c [generic x, generic xs])
> dCons _ _      = Nothing
>
> infixr 5 ^:
> nil  :: (Monad m, Generic a) => Nondet c m [a]
> (^:) :: (Monad m, Generic a)
>      => Nondet c m a -> Nondet c m [a] -> Nondet c m [a]
> nil :! (^:) :! () = constructors
>
> pNil  :: Generic a => (Context c -> Nondet c m b) -> Match [a] c m b
> pCons :: Generic a
>       => (Context c -> Nondet c m a -> Nondet c m [a] -> Nondet c m b)
>       -> Match [a] c m b
> pNil :! pCons :! () = patterns

We can use logic variables of a list type if there are logic variables
for the element type.

> instance (Narrow a, Generic a) => Narrow [a]
>  where
>   narrow cs u = withUnique (\u1 u2 -> 
>                   (oneOf [nil, unknown u1 ^: unknown u2] cs u)) u

Some operations on lists:

> null :: (CFLP s, Generic a)
>      => Data s [a] -> Context (Ctx s) -> Data s Bool
> null xs = caseOf_ xs [pNil (const true)] false
>
> head :: (CFLP s, Generic a)
>      => Data s [a] -> Context (Ctx s) -> Data s a
> head l = caseOf l [pCons (\_ x _ -> x)]
>
> tail :: (CFLP s, Generic a)
>      => Data s [a] -> Context (Ctx s) -> Data s [a]
> tail l = caseOf l [pCons (\_ _ xs -> xs)]

Higher-order functions:

> map :: (CFLP s, Generic a, Generic b)
>     => Data s (a -> b) -> Data s [a] -> Context (Ctx s) -> ID -> Data s [b]
> map f l cs = withUnique $ \u ->
>               foldr (fun (\x xs -> apply f x cs u ^: xs)) nil l cs
>
> foldr :: (CFLP s, Generic a)
>       => Data s (a -> b -> b) -> Data s b -> Data s [a]
>       -> Context (Ctx s) -> ID -> Data s b
> foldr f y l cs = withUnique $ \u1 u2 u3 ->
>   caseOf l
>     [ pNil (const y)
>     , pCons (\cs x xs -> apply (apply f x cs u1) (foldr f y xs cs u2) cs u3)
>     ] cs

