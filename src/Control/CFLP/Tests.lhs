% Testing the `cflp` Package
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines auxiiary functions for the test suite.

> module Control.CFLP.Tests where
>
> import Control.CFLP
> import Control.Monad.Constraint
> import Test.HUnit

We use HUnit for testing because we need to test IO actions and want
to use errors when testing laziness.

> assertResults :: (Data a, Show a, Eq a)
>               => (EvalStore -> ID -> Nondet (ConstrT EvalStore []) a)
>               -> [a] -> Assertion
> assertResults = assertResultsLimit Nothing
>
> assertResultsN 
>   :: (Data a, Show a, Eq a)
>   => Int
>   -> (EvalStore -> ID -> Nondet (ConstrT EvalStore []) a)
>   -> [a] -> Assertion
> assertResultsN = assertResultsLimit . Just
>
> assertResultsLimit 
>   :: (Data a, Show a, Eq a)
>   => Maybe Int
>   -> (EvalStore -> ID -> Nondet (ConstrT EvalStore []) a)
>   -> [a] -> Assertion
> assertResultsLimit limit op expected = do
>   actual <- eval depthFirst op
>   maybe id take limit actual @?= expected

We provide auxiliary assertions `assertResults...` that compute (a
possibly limited number of) non-deterministic results of a functional
logic computation in depth-first order and compare them with a list of
given expected results.

