% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a datatype with operations for lazy
non-deterministic programming.

> module Data.LazyNondet (
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
> import Data.LazyNondet.Types
> import Data.LazyNondet.Generic
> import Data.LazyNondet.UniqueID
> import Data.LazyNondet.Matching
> import Data.LazyNondet.Narrowing
> import Data.LazyNondet.Primitive
> import Data.LazyNondet.HigherOrder
