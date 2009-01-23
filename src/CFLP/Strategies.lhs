% Strategies for Constraint Functional-Logic Programming
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module exposes strategies for CFLP by re-exporting them from
other modules in this package.

> {-# LANGUAGE
>       FlexibleInstances
>   #-}
>
> module CFLP.Strategies (
>
>   (+>), dfs,
>
>   module CFLP.Strategies.DepthFirst,
>   module CFLP.Strategies.CallTimeChoice,
>   module CFLP.Strategies.DepthCounter
>
>  ) where
>
> import Control.Monad
>
> import CFLP
> import CFLP.Strategies.DepthFirst
> import CFLP.Strategies.CallTimeChoice
> import CFLP.Strategies.DepthCounter

We provide a combinator `(+>)` to transform a strategy with a strategy
transformer (the type is not descriptive, so better ignore it..).

> infixl 5 +>
>
> (+>) :: (a -> b) -> (b -> c) -> d -> c
> (s +> t) _ = t (s undefined)

For convenience, we provide shortcuts for useful strategies.

> dfs :: c -> CTC (Monadic (UpdateT (StoreCTC c) [])) a
> dfs = dfsWithEvalTimeChoice +> callTimeChoice

Finally, we provide instances for the type class `CFLP` that is a
shortcut for the class constraints of CFLP computations.

> instance (MonadPlus m, Enumerable m)
>       => CFLP (CTC (Monadic (UpdateT (StoreCTC ()) m)))

