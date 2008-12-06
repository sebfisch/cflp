% Testing the `cflp` Package
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% December, 2008

This module defines auxiiary functions for the test suite.

> module Control.CFLP.Tests where
>
> import Control.CFLP
> import Control.Monad.Constraint
> import Test.HUnit

We use HUnit for testing because we need to test IO actions and want
to use errors when testing laziness.

> assertResults :: (Data a, Show a, Eq a)
>               => (EvalStore -> ID -> Typed (ConstrT EvalStore []) a)
>               -> [a] -> Assertion
> assertResults op expected = do
>   actual <- eval depthFirst op
>   actual @?= expected

We provide an auxiliary assertion `assertResults` that computes the
non-deterministic results of a functional logic computation in depth
first order and compares them with a list of given expected results.
