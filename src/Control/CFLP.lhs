% Constraint Functional-Logic Programming
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides an interface that can be used for constraint
functional-logic programming in Haskell.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       RankNTypes
>   #-}
>
> module Control.CFLP (
>
>   CFLP, EvalStore, eval, evalPrint,
>
>   Strategy, depthFirst,
>
>   module Data.LazyNondet,
>   module Data.LazyNondet.Bool,
>   module Data.LazyNondet.List
>
> ) where
>
> import Data.LazyNondet
> import Data.LazyNondet.Bool
> import Data.LazyNondet.List
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> class (MonadConstr Choice m,
>        ConstraintStore Choice cs,
>        MonadSolve cs m m)
>  => CFLP cs m

The type class `CFLP` is a shortcut for the type-class constraints on
constraint functional-logic operations.

> instance CFLP ChoiceStore (ConstrT ChoiceStore [])

We declare instances for every combination of monad and constraint
store that we intend to use.

> type EvalStore = ChoiceStore
>
> noConstraints :: EvalStore
> noConstraints = noChoices

Currently, the constraint store used to evaluate constraint
functional-logic programs is simply a `ChoiceStore`. It will be a
combination of different constraint stores, when more constraint
solvers have been implemented.

> type Strategy m = forall a . m a -> [a]

A `Strategy` specifies how to enumerate non-deterministic results in a
list.

> depthFirst :: Strategy []
> depthFirst = id

The strategy of the list monad is depth-first search.

> eval :: (CFLP EvalStore m, MonadSolve EvalStore m m', Data a)
>      => Strategy m' -> (EvalStore -> ID -> Nondet m a)
>      -> IO [a]
> eval enumerate op = do
>   i <- initID
>   return (enumerate (normalForm (op noConstraints i) noConstraints))

The `eval` function enumerates the non-deterministic solutions of a
constraint functional-logic computation according to a given strategy.

> evalPrint :: (CFLP EvalStore m, MonadSolve EvalStore m m', Data a, Show a)
>           => Strategy m' -> (EvalStore -> ID -> Nondet m a)
>           -> IO ()
> evalPrint s op = eval s op >>= printSols
>
> printSols :: Show a => [a] -> IO ()
> printSols []     = putStrLn "No more solutions."
> printSols (x:xs) = do
>   print x
>   putStr "more? [Y|n]: "
>   s <- getLine
>   if s `elem` ["n","no"] then return () else printSols xs

For convenience, we provide an `evalPrint` operation that
interactively shows solutions of a constraint functional-logic
computation.

