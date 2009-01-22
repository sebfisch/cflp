% Testing Call-Time Choice of Functional-Logic Operations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines tests that specify the intended behaviour of
functional-logic programs w.r.t. laziness and sharing. Although
non-deterministic computations must be executed on demand, their
results have to be as if they were executed eagerly.

> module CFLP.Tests.CallTimeChoice where
>
> import CFLP
> import CFLP.Tests
>
> import Test.HUnit
>
> import Prelude hiding ( not, null, head )
> import CFLP.Types.Bool
> import CFLP.Types.List

Every module under `CFLP.Tests` defines a constant `tests` that
collects all defined tests.

> tests :: Test
> tests = "call-time choice" ~: test
>   [ "ignore first, narrow second" ~: ignoreFirstNarrowSecond
>   , "shared vars are equal" ~: sharedVarsAreEqual
>   , "no demand on shared var" ~: noDemandOnSharedVar
>   , "shared compound terms" ~: sharedCompoundTerms
>   ]

The following test checks a function with two arguments, where the
first must be ignored. Any changes in the translation scheme must not
lead to demand on the first argument of `ignot`. I have no better idea
to check demand than with using `error`. So an *error* is considered a
*failure* in this test case.

> ignoreFirstNarrowSecond :: Assertion
> ignoreFirstNarrowSecond = assertResults comp [True,False]
>  where
>   comp cs u = ignot (error "illegal demand") (unknown u) cs
>
> ignot :: CFLP s
>       => Data s a -> Data s Bool -> Context (Ctx s) -> Data s Bool
> ignot _ = not

The following test checks call-time choice semantics: variables
represent identical ground values. The elements of the constructed
list must be equal although they are computed from a free variable.

> sharedVarsAreEqual :: Assertion
> sharedVarsAreEqual = assertResults comp [[False,False],[True,True]]
>  where
>   comp _ = two . unknown
>
> two :: (Monad m, Generic a) => Nondet cs m a -> Nondet cs m [a]
> two x = x ^: x ^: nil

In the current translation scheme sharing is implicit (we have no
special combinator to express sharing but use Haskell's sharing
directly). In case we introduce such a combinator, the following tests
are interesting.

Even with an explicit combinator for sharing (to be used, e.g., in the
definition of the function `two`) there must not be demand on
something that is shared.

> noDemandOnSharedVar :: Assertion
> noDemandOnSharedVar = assertResults comp [False]
>  where
>   comp cs _ = null (two (error "illegal demand" :: Nondet cs m Bool)) cs

The following test checks whether sharing is ensured on aruments of
compound terms even if they are consumed. In this example, the
variable `l` is shared, so the heads that are computed twice must be
equal and the negated head must be different from the head.

> sharedCompoundTerms :: Assertion
> sharedCompoundTerms = assertResults comp [[True,False],[False,True]]
>  where
>   comp cs u = negHeads (unknown u) cs
>
> negHeads :: CFLP s
>          => Data s [Bool] -> Context (Ctx s) -> Data s [Bool]
> negHeads l cs = not (head l cs) cs ^: head l cs ^: nil
