% Permutation Sort
% [Sebastian Fischer](mailto:sebf@informatik.uni-kiel.de)
% November, 2008

This module defines the permutation sort function in order to
demonstrate the use of our library for functional logic programming.

~~~ { .LiterateHaskell }

> {-# OPTIONS -XFlexibleContexts #-}
>
> import Control.LazyFLP
>
> insert :: FLP t cs m
>        => Typed (t cs m) a -> Typed (t cs m) [a]
>        -> cs -> ID -> ID
>        -> Typed (t cs m) [a]
> insert x xs cs i1 i2 = oneOf
>   [ x ^: xs
>   , caseOf xs (\xs' cs' ->
>     case xs' of
>       Cons _ 1 _ -> x ^: nil
>       Cons _ 2 [y,ys] -> Typed y ^: call (insert x (Typed ys) cs') i1) cs
>   ] i2

~~~

