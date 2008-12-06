% Cabal Setup File for the `cflp` Package
% Sebastian Fischer (sebf@informatik.uni-kiel.de)
% November, 2008

> import System.Process
> import System.Exit
> import Distribution.Simple
>
> main = defaultMainWithHooks $ simpleUserHooks { runTests = runTestSuite }
>
> runTestSuite _ _ _ _ =
>   runCommand "runhaskell -i.:src Test.lhs" >>= waitForProcess >>= exitWith


