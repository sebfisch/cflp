% Testing Boolean Constraints in CFLP
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines tests that show how to use boolean constraints in
constraint functional-logic programs.

> {-# LANGUAGE
>       FlexibleContexts
>   #-}
>
> module CFLP.Tests.Boolean where
>
> import Test.HUnit
>
> import CFLP
> import CFLP.Tests
>
> import CFLP.Strategies
> import CFLP.Constraints.Boolean
>
> import Prelude hiding ( map )
> import CFLP.Types.Bool
> import CFLP.Types.List
>
> tests :: Test
> tests = "boolean constraints" ~: test
>   [ "assert variable" ~: assertVariable,
>     "x and y and z" ~: xAndYandZ,
>     "unsatisfiable" ~: unsatisfiable,
>     "unsatisfiable with backtracking" ~: unsatisfiableWithBacktracking
>   ]

This tests asserts a logic variable and queries it afterwards.

> assertVariable :: Assertion
> assertVariable = assertResults comp [True]
>  where
>   comp :: Computation Bool
>   comp c u = let x = unknown u in ifThen x (booleanToBool x c) c

This test queries all solutions to the formula `x && y || z`.

> xAndYandZ :: Assertion
> xAndYandZ = assertResults comp [[True,True,True]]
>  where
>   comp :: Computation [Bool]
>   comp c = withUnique $ \u1 u2 u3 u4 ->
>              let x = unknown u1
>                  y = unknown u2
>                  z = unknown u3
>               in ifThen (x.&&.y.&&.z)
>                         (map (fun booleanToBool) (x^:y^:z^:nil) c u4) c

This tests asserts an unsatisfiable formula.

> unsatisfiable :: Assertion
> unsatisfiable = assertResults comp []
>  where
>   comp :: Computation [Bool]
>   comp c = withUnique $ \u1 u2 u3 u4 ->
>              let x = unknown u1
>                  y = unknown u2
>                  z = unknown u3
>                  vars = map (fun booleanToBool) (x^:y^:z^:nil) c u4
>                  formula = (neg x .||. y)
>                       .&&. (x .||. neg y)
>                       .&&. (neg y .||. z)
>                       .&&. (y .||. neg z)
>                       .&&. (neg x .||. neg z)
>                       .&&. (x .||. z)
>               in ifThen formula vars c

This test asserts an unsatisfiable formula that is only detected as
such after backtracking.

> unsatisfiableWithBacktracking :: Assertion
> unsatisfiableWithBacktracking = assertResults comp []
>  where
>   comp :: Computation Bool
>   comp c = withUnique $ \u1 u2 ->
>              let x = unknown u1
>                  y = unknown u2
>                  formula = (x .&&. neg x) .||. (y .&&. neg y)
>               in ifThen formula true c


