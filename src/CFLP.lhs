% Constraint Functional-Logic Programming
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides an interface that can be used for constraint
functional-logic programming in Haskell.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies,
>       RankNTypes
>   #-}
>
> module CFLP (
>
>   CFLP, Enumerable(..), Ctx, Data,
>
>   eval, evalPartial, evalPrint,
>
>   Monadic, monadic, UpdateT,
>
>   module CFLP.Data
>
> ) where
>
> import Control.Monad.State
>
> import CFLP.Data
> import CFLP.Data.Types
>
> import CFLP.Control.Monad.Update
>
> import CFLP.Control.Strategy

The type class `CFLP` amalgamates all class constraints on constraint
functional-logic computations.

> class (Strategy (Ctx s) s, MonadPlus s
>                          , Solvable (Ctx s)
>                          , MonadUpdate (Ctx s) s
>                          , Update (Ctx s) s s
>                          , Update (Ctx s) s (Res s)
>                          , MonadPlus (Res s)
>                          , Enumerable (Res s))
>    => CFLP s
>
> monadic :: Monad m => Monadic (UpdateT c m) ()
> monadic = Monadic (return ())
>
> instance (MonadPlus m, Enumerable m) => CFLP (Monadic (UpdateT () m))

We define a shortcut for types of constraint functional-logic data
that can be parameterized by an arbitrary strategy.

> type Data s a = Nondet (Ctx s) s a

We provide

  * an `eval` operation to compute Haskell terms from
    non-deterministic data,

  * an operation `evalPartial` to compute partial Haskell terms where
    logic variables are replaced with an error, and

  * an `evalPrint` operation that interactively shows (partial)
    solutions of a constraint functional-logic computation.

> eval, evalPartial
>   :: (Monad s, CFLP s, Generic a)
>   => [s (Ctx s)]
>   -> (Context (Ctx s) -> ID -> Data s a)
>   -> IO [a]
> eval        s = liftM (liftM primitive) . evaluate s groundNormalForm
> evalPartial s = liftM (liftM primitive) . evaluate s partialNormalForm
>
> evalPrint :: (Monad s, CFLP s, Generic a)
>           => [s (Ctx s)] -> (Context (Ctx s) -> ID -> Data s a) -> IO ()
> evalPrint s op = evaluate s partialNormalForm op >>= printSols
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

The `evaluate` function enumerates the non-deterministic solutions of a
constraint functional-logic computation according to a given strategy.

> evaluate :: CFLP s
>          => [s (Ctx s)]
>          -> (s (Ctx s) -> Nondet (Ctx s) s a -> Res s (b, Ctx s))
>          -> (Context (Ctx s) -> ID -> Data s a)
>          -> IO [b]
> evaluate s evalNondet op = do
>   i <- initID
>   return $ concatMap enumeration $ map (run i) s
>  where
>   run i c = do
>     (res,ctx) <- evalNondet c (Typed (c >>= untyped . flip op i . Context))
>     guard (solvable ctx)
>     return res
