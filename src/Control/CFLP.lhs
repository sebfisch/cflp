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
>   CFLP, CS, Computation, eval, evalPartial, evalPrint,
>
>   Strategy, depthFirst,
>
>   module Data.LazyNondet,
>   module Data.LazyNondet.Types.Bool,
>   module Data.LazyNondet.Types.List
>
> ) where
>
> import Data.LazyNondet
> import Data.LazyNondet.Primitive
> import Data.LazyNondet.Types.Bool
> import Data.LazyNondet.Types.List
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> class (MonadConstr Choice m,
>        ConstraintStore Choice cs,
>        ChoiceStore cs,
>        MonadSolve cs m m)
>  => CFLP cs m

The type class `CFLP` is a shortcut for the type-class constraints on
constraint functional-logic computations that are parameterized over a
constraint store and a constraint monad. Hence, such computations can
be executed with different constraint stores and search strategies.

> instance CFLP ChoiceStoreUnique (ConstrT ChoiceStoreUnique [])

We declare instances for every combination of monad and constraint
store that we intend to use.

> type CS = ChoiceStoreUnique
>
> noConstraints :: CS
> noConstraints = noChoices
>
> type Computation m a = CS -> ID -> Nondet CS (ConstrT CS m) a

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

> evaluate :: (CFLP CS m, MonadSolve CS m m')
>          => (Nondet CS m a -> CS -> m' b)
>          -> Strategy m' -> (CS -> ID -> Nondet CS m a)
>          -> IO [b]
> evaluate evalNondet enumerate op = do
>   i <- initID
>   return $ enumerate $ evalNondet (op noConstraints i) noConstraints

The `evaluate` function enumerates the non-deterministic solutions of a
constraint functional-logic computation according to a given strategy.

> eval, evalPartial :: (CFLP CS m, MonadSolve CS m m', Data a)
>                   => Strategy m' -> (CS -> ID -> Nondet CS m a)
>                   -> IO [a]
> eval        s = liftM (map prim) . evaluate groundNormalForm  s
> evalPartial s = liftM (map prim) . evaluate partialNormalForm s
>
> evalPrint :: (CFLP CS m, MonadSolve CS m m', Data a, Show a)
>           => Strategy m' -> (CS -> ID -> Nondet CS m a)
>           -> IO ()
> evalPrint s op = evaluate groundNormalForm s op >>= printSols
>
> printSols :: Show a => [a] -> IO ()
> printSols []     = putStrLn "No more solutions."
> printSols (x:xs) = do
>   print x
>   putStr "more? [Y(es)|n(o)|a(ll)]: "
>   s <- getLine
>   if s `elem` ["n","no"] then
>     return ()
>    else if s `elem` ["a","all"]
>     then mapM_ print xs
>     else printSols xs

We provide

  * an `eval` operation to compute Haskell terms from non-determinitic
    data,

  * an operation `evalPartial` to compute partial Haskell terms where
    logic variables are replaced with an error, and

  * an `evalPrint` operation that interactively shows (partial)
    solutions of a constraint functional-logic computation.

