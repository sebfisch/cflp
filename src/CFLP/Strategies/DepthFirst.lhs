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
> module CFLP.Strategies.DepthFirst ( dfs ) where
>
> import CFLP
>
> import CFLP.Strategies.CallTimeChoice

Depth-first search is implemented by the list monad. In order to make
it a strategy, we need to make `[]` an instance of the `Enumerable`
type class that allows to enumerate monadic values in a list. For the
list monad, this instance is trivial:

> instance Enumerable [] where enumeration = id

We define depth-first search strategies for evaluation-time and
call-time choice semantics. Each strategy takes an argument that is
used to fix the type of the evaluation context. It is safe to pass
`undefined` there. When extending a strategy one passes `undefined`
when using a strategy to evaluate results of a CFLP computation, one
needs to pass `()`.

> dfsWithEvalTimeChoice :: c -> Monadic (UpdateT c []) a
> dfsWithEvalTimeChoice _ = Monadic undefined
>
> dfs :: c -> CTC (Monadic (UpdateT (StoreCTC c) [])) a
> dfs _ = CTC (dfsWithEvalTimeChoice undefined)
