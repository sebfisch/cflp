% Strategies for Constraint Functional-Logic Programming
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module exposes strategies for CFLP by re-exporting them from
other modules in this package.

> {-# LANGUAGE
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies,
>       RankNTypes
>   #-}
>
> module CFLP.Strategies (
>
>   Computation,
>
>   dfs, limDFS, iterDFS, bfs, diag, fair, rndDFS,
>
>   dfs_B, limDFS_B, iterDFS_B, bfs_B, diag_B, fair_B, rndDFS_B
>
>  ) where
>
> import Control.Monad.Logic
> import Control.Monad.Omega
> import Control.Monad.Levels
> import Control.Monad.Stream
>
> import CFLP
> import CFLP.Strategies.CallTimeChoice
> import CFLP.Strategies.DepthCounter
> import CFLP.Strategies.DepthLimit
> import CFLP.Strategies.Random
>
> import CFLP.Constraints.Boolean

We provide shortcuts for useful strategies.

depth-first search:

> instance Enumerable []    where enumeration = id
> instance Enumerable Logic where enumeration = observeAll
> -- using `Logic` instead of `[]` destroys sharing. Investigate.
> dfs :: [CTC (Monadic (UpdateT (StoreCTC ()) [])) (StoreCTC ())]
> dfs = [callTimeChoice monadic]

depth-first search with limited depth:

> limDFS :: Int
>        -> [CTC (Depth (DepthLim (Monadic
>                 (UpdateT (StoreCTC (DepthCtx (DepthLimCtx ()))) []))))
>                (StoreCTC (DepthCtx (DepthLimCtx ())))]
> limDFS l = [limitedDepthFirstSearch l]
>
> limitedDepthFirstSearch
>  :: Int -> CTC (Depth (DepthLim (Monadic
>                  (UpdateT (StoreCTC (DepthCtx (DepthLimCtx ()))) []))))
>                (StoreCTC (DepthCtx (DepthLimCtx ())))
> limitedDepthFirstSearch l
>   = callTimeChoice . countDepth . limitDepth l $ monadic

iterative deepening depth-first search:

> iterDFS :: [CTC (Depth (DepthLim (Monadic
>                   (UpdateT (StoreCTC (DepthCtx (DepthLimCtx ()))) []))))
>                 (StoreCTC (DepthCtx (DepthLimCtx ())))]
> iterDFS = map limitedDepthFirstSearch [0..]

breadth-first search:

> instance Enumerable Levels where enumeration = breadthFirstSearch
>
> bfs :: [CTC (Monadic (UpdateT (StoreCTC ()) Levels)) (StoreCTC ())]
> bfs = [callTimeChoice monadic]

Fair diagonalization by Luke Palmer:

> instance Enumerable Omega where enumeration = runOmega
>
> diag :: [CTC (Monadic (UpdateT (StoreCTC ()) Omega)) (StoreCTC ())]
> diag = [callTimeChoice monadic]

Fair interleaving by Oleg Kiselyov:

> instance Enumerable Stream where enumeration = runStream
>
> fair :: [CTC (Monadic (UpdateT (StoreCTC ()) Stream)) (StoreCTC ())]
> fair = [callTimeChoice monadic]

We combine randomization with depth-first search. Here, it is crucial
to use the call-time choice transformer *before* the randomizer
shuffles choices.

> rndDFS :: [CTC (Rnd (Monadic (UpdateT (StoreCTC (RndCtx ())) [])))
>                (StoreCTC (RndCtx ()))]
> rndDFS = [callTimeChoice . randomise $ monadic]

depth-first search with boolean constraints:

> dfs_B :: [CTC (Sat (Monadic (UpdateT (StoreCTC (SatCtx ())) [])))
>               (StoreCTC (SatCtx ()))]
> dfs_B = [callTimeChoice . satSolving $ monadic]

depth-first search with boolean constraints and limited depth:

> limDFS_B :: Int
>          -> [CTC (Depth (DepthLim (Sat (Monadic
>                   (UpdateT (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))
>                            [])))))
>                  (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))]
> limDFS_B l = [limitedDepthFirstSearch_B l]
>
> limitedDepthFirstSearch_B
>  :: Int -> CTC (Depth (DepthLim (Sat (Monadic
>                  (UpdateT (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))
>                           [])))))
>                (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))
> limitedDepthFirstSearch_B l
>   = callTimeChoice . countDepth . limitDepth l . satSolving $ monadic

iterative deepening depth-first search with boolean constraints:

> iterDFS_B :: [CTC (Depth (DepthLim (Sat (Monadic
>                     (UpdateT (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))
>                              [])))))
>                   (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))]
> iterDFS_B = map limitedDepthFirstSearch_B [0..]

breadth-first search with boolean constraints:

> bfs_B :: [CTC (Sat (Monadic (UpdateT (StoreCTC (SatCtx ())) Levels)))
>               (StoreCTC (SatCtx ()))]
> bfs_B = [callTimeChoice . satSolving $ monadic]

Fair diagonalization by Luke Palmer with boolean constraints:

> diag_B :: [CTC (Sat (Monadic (UpdateT (StoreCTC (SatCtx ())) Omega)))
>                (StoreCTC (SatCtx ()))]
> diag_B = [callTimeChoice . satSolving $ monadic]

Fair interleaving by Oleg Kiselyov with boolean constraints:

> fair_B :: [CTC (Sat (Monadic (UpdateT (StoreCTC (SatCtx ())) Stream)))
>                (StoreCTC (SatCtx ()))]
> fair_B = [callTimeChoice . satSolving $ monadic]

We combine randomization with depth-first search. Here, it is crucial
to use the call-time choice transformer *before* the randomizer
shuffles choices.

> rndDFS_B :: [CTC (Rnd (Sat (Monadic (UpdateT (StoreCTC (RndCtx (SatCtx ())))
>                                         []))))
>                  (StoreCTC (RndCtx (SatCtx ())))]
> rndDFS_B = [callTimeChoice . randomise . satSolving $ monadic]

Finally, we provide instances for the type class `CFLP` that is a
shortcut for the class constraints of CFLP computations.

> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Monadic (UpdateT (StoreCTC ()) m)))
>
> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Depth (DepthLim (Monadic
>                     (UpdateT (StoreCTC (DepthCtx (DepthLimCtx ()))) m)))))
>
> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Rnd (Monadic (UpdateT (StoreCTC (RndCtx ())) m))))
>
> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Sat (Monadic (UpdateT (StoreCTC (SatCtx ())) m))))
>
> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Depth (DepthLim (Sat (Monadic
>                     (UpdateT (StoreCTC (DepthCtx (DepthLimCtx (SatCtx ()))))
>                              m))))))
>
> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Rnd (Sat (Monadic (UpdateT
>                                        (StoreCTC (RndCtx (SatCtx ())))
>                                        m)))))

We also define a shortcut for computations.

> type Computation a
>   = forall s . (CFLP s, BooleanSolver (Ctx s)) =>
>     Context (Ctx s) -> ID -> Data s a

