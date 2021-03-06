% Testing the `cflp` Package
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines auxiliary functions for the test suite.

> {-# LANGUAGE
>       FlexibleContexts,
>       RankNTypes
>   #-}
>
> module CFLP.Tests where
>
> import CFLP
> import CFLP.Strategies
>
> import Test.HUnit

We use HUnit for testing because we need to test IO actions and want
to use errors when testing laziness.

> assertResults :: (Generic a, Show a, Eq a)
>               => Computation a -> [a] -> Assertion
> assertResults = assertResultsLimit Nothing
>
> assertResultsN :: (Generic a, Show a, Eq a)
>                => Int -> Computation a -> [a] -> Assertion
> assertResultsN = assertResultsLimit . Just
>
> assertResultsLimit :: (Generic a, Show a, Eq a)
>                    => Maybe Int -> Computation a -> [a] -> Assertion
> assertResultsLimit limit op expected = do
>   actual <- eval (limDFS_B 100) op
>   maybe id take limit actual @?= expected

We provide auxiliary assertions `assertResults...` that compute (a
possibly limited number of) non-deterministic results of a functional
logic computation in depth-first order and compare them with a list of
given expected results.

