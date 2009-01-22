% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a datatype with operations for lazy
non-deterministic programming.

> module CFLP.Data (
>
>   NormalForm, Nondet, Context(..),
>
>   ID, initID, withUnique,
>
>   Narrow(..), unknown, 
>
>   failure, oneOf, (?),
>
>   withHNF, caseOf, caseOf_, Match,
>
>   Generic(..), primitive, generic, nondet,
>
>   Decons, ApplyCons(..), (!), cons,
>
>   groundNormalForm, partialNormalForm,
>
>   ConsPatList(..), constructors, patterns,
>
>   apply, fun
>
> ) where
>
> import CFLP.Data.Types
> import CFLP.Data.Generic
> import CFLP.Data.UniqueID
> import CFLP.Data.Matching
> import CFLP.Data.Narrowing
> import CFLP.Data.Primitive
> import CFLP.Data.HigherOrder
