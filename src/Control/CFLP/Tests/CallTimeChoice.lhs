% Testing Call-Time Choice of Functional-Logic Operations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% December, 2008

This module defines tests that specify the intended behaviour of
functional-logic programs w.r.t. laziness and sharing. Although
non-deterministic computations must be executed on demand, their
results have to be as if they were executed eagerly.

> module Control.CFLP.Tests.CallTimeChoice where
>
> import Control.CFLP
> import Control.CFLP.Tests
> import Test.HUnit
>
> import Prelude hiding ( not )
>
> tests :: Test
> tests = "call-time choice" ~: test
>  [ "ignore first, narrow second" ~: ignoreFirstNarrowSecond ]

Every module under `Control.CFLP.Tests` defines a constant `tests`
that collects all defined tests.

> ignoreFirstNarrowSecond :: Assertion
> ignoreFirstNarrowSecond = assertResults comp [True,False]
>  where
>   comp cs = withUnique (\u -> ignot (error "illegal demand") (unknown u) cs)
>
> ignot :: CFLP cs t m
>       => Typed (t cs m) a -> Typed (t cs m) Bool
>       -> cs -> Typed (t cs m) Bool
> ignot _ x = not x

This test checks a function with two arguments, where the first must
be ignored. Any changes in the translation scheme must not lead to
demand on the first argument of `ignot`. I have no better idea to
check demand than with using `error`. So an *error* is considered a
*failure* in this test case.


