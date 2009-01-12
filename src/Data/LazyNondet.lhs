% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a datatype with operations for lazy
non-deterministic programming.

> module Data.LazyNondet (
>
>   NormalForm, Nondet,
>
>   ID, initID, withUnique,
>
>   Narrow(..), unknown, 
>
>   failure, oneOf, (?),
>
>   withHNF, caseOf, caseOf_, Match,
>
>   Data, nondetData, primData, groundNormalForm, partialNormalForm,
>
>   ConsRep(..), cons, match,
>
> ) where
>
> import Data.Data
> import Data.LazyNondet.Types
> import Data.LazyNondet.UniqueID
> import Data.LazyNondet.Matching
> import Data.LazyNondet.Narrowing
> import Data.LazyNondet.Primitive
