% Testing the `cflp` Package
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module is used in the hook that runs the tests for the `cflp`
package.

> import Test.HUnit
>
> import CFLP.Tests.CallTimeChoice as CTC
> import CFLP.Tests.HigherOrder as HO
> import CFLP.Tests.Boolean as B
>
> main :: IO ()
> main = do
>  runTestTT $ test [CTC.tests,HO.tests,B.tests]
>  return ()

