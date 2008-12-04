% Constraint Functional-Logic Programming
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% November, 2008

This module provides an interface that can be used for constraint
functional-logic programming in Haskell.

> {-# OPTIONS
>      -XMultiParamTypeClasses
>      -XFlexibleInstances
>      -XFlexibleContexts
>      -XRankNTypes
>   #-}
>
> module Control.CFLP (
>
>   CFLP, Evaluator, evalPrint,
>
>   depthFirst, depthFirst',
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
> class (MonadConstr Choice (t cs m), RunConstr cs m t) => CFLP cs t m

The type class `CFLP` is a shortcut for the type-class constraints on
constraint functional-logic operations.

> type EvalStore = ChoiceStore
>
> noConstraints :: EvalStore
> noConstraints = noChoices

Currently, the constraint store used to evaluate constraint
functional-logic program is simply a `ChoiceStore`. It will be a
combination of different constraint stores, when more constraint
solvers have been implemented.

> newtype CFLP EvalStore t m => Evaluator t m
>  = Eval { enumerate :: forall a . m a -> [a] }

An `Evaluator` specifies via phantom types which constraint collecting
monad to use. It wraps an enumeration function that collects
non-deterministic results in a list.

> instance CFLP ChoiceStore ConstrT []
>
> depthFirst :: Evaluator ConstrT []
> depthFirst = Eval id
>
> instance CFLP ChoiceStore StateT []
>
> depthFirst' :: Evaluator StateT []
> depthFirst' = Eval id

With a transformed list monad we get depth first search.

> eval :: (CFLP EvalStore t m, Data a)
>      => Evaluator t m -> (EvalStore -> ID -> Typed (t EvalStore m) a)
>      -> IO [a]
> eval e op = do
>   i <- initID
>   return (enumerate e (normalForm (op noConstraints i) noConstraints))

The `eval` function enumerates the non-deterministic solutions of a
constraint functional-logic computation.

> evalPrint e op = eval e op >>= printSols
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