% Depth-First Search for Constraint Functional-Logic Programs
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines depth-first search as a strategy that can be used
in constraint functional-logic programs.

It shows what definitions are necessary in order to turn an instance
of the `MonadPlus` type class into a strategy for CFLP.

> {-# LANGUAGE
>       FlexibleInstances
>   #-}
>
> module CFLP.Strategies.DepthFirst where
>
> import CFLP

Depth-first search is implemented by the list monad. In order to make
it a strategy, we need to make `[]` an instance of the `Enumerable`
type class that allows to enumerate monadic values in a list. For the
list monad, this instance is trivial:

> instance Enumerable [] where enumeration = id

We define depth-first search strategies for evaluation-time choice
semantics. In order to get call-time choice, this needs to be
transformed with the call-time choice transformer.

> dfsWithEvalTimeChoice :: c -> Monadic (UpdateT c []) a
> dfsWithEvalTimeChoice _ = Monadic undefined

