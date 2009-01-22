% Strategies for Constraint Functional-Logic Programming
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module exposes strategies for CFLP by re-exporting them from
other modules in this package.

> module CFLP.Strategies (
>
>   (+>), dfs,
>
>   module CFLP.Strategies.DepthFirst,
>   module CFLP.Strategies.CallTimeChoice
>
>  ) where
>
> import CFLP
> import CFLP.Strategies.DepthFirst
> import CFLP.Strategies.CallTimeChoice

We provide a combinator `(+>)` to transform a strategy with a strategy
transformer (the type is not descriptive, so better ignore it..).

> infixl 5 +>
>
> (+>) :: (a -> b) -> (b -> c) -> d -> c
> (s +> t) _ = t (s undefined)

For convenience, we provide shortcuts for useful strategies.

> dfs :: c -> CTC (Monadic (UpdateT (StoreCTC c) [])) a
> dfs = dfsWithEvalTimeChoice +> callTimeChoice

