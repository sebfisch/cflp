% Testing Higher-Order Functional-Logic Operations
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module defines tests that show how to define higher-order
functional-logic programs.

> module Control.CFLP.Tests.HigherOrder where
>
> import Control.CFLP
> import Control.CFLP.Tests
> import Test.HUnit
>
> import Prelude hiding ( not, null, head, map, foldr, flip, id )
> import qualified Prelude as P
> import Data.LazyNondet.Types.Bool
> import Data.LazyNondet.Types.List
>
> tests :: Test
> tests = "higher order" ~: test
>   [ "apply not function" ~: applyNotFunction
>   , "apply binary constructor" ~: applyBinCons
>   , "apply non-deterministic choice" ~: applyChoice
>   , "call-time choice" ~: callTimeChoice
>   , "map shared unknowns" ~: mapSharedUnknowns
>   , "memeber with fold" ~: memberWithFold
>   , "overApplication" ~: overApplication
>   , "reverse with foldr" ~: reverseWithFoldr
>   -- , "pointfree reverse" ~: pointfreeReverse
>   -- , "function conversion" ~: functionConversion
>   ]

The following test simply applies the not function.

> applyNotFunction :: Assertion
> applyNotFunction = assertResults comp [True]
>  where
>   comp = apply (fun not) false

The following test applies the binary list constructor.

> applyBinCons :: Assertion
> applyBinCons = assertResults comp [[True]]
>  where
>   comp cs = withUnique $ \u1 u2 ->
>               apply (apply (fun (^:)) true cs u1) nil cs u2

The following tests applies the binary operator for non-deterministic
choice.

> applyChoice :: Assertion
> applyChoice = assertResults comp [False,True]
>  where
>   comp cs = withUnique $ \u1 u2 ->
>               apply (apply (fun (?)) false cs u1) true cs u2

The following test checks whether call-time choice is still obtained
when applying the choice combinator using higher-order features.

> callTimeChoice :: Assertion
> callTimeChoice = assertResults comp [[False,False],[True,True]]
>  where
>   comp cs = withUnique $ \u1 u2 u3 ->
>               apply (fun two)
>                     (apply (apply (fun (?)) false cs u1) true cs u2) cs u3
>
> two :: (Monad m, Generic a) => Nondet cs m a -> Nondet cs m [a]
> two x = x ^: x ^: nil

The following test maps the function `not` over a list with a
duplicated free variable.

> mapSharedUnknowns :: Assertion
> mapSharedUnknowns = assertResults comp [[True,True],[False,False]]
>  where
>   comp cs = withUnique $ \u -> map (fun not) (two (unknown u)) cs

The following test checks the member operation defined using `foldr`.

> memberWithFold :: Assertion
> memberWithFold = assertResults comp [True,False]
>  where
>   comp = foldr (fun (?)) failure (true ^: false ^: nil)

The following test applies the composition function which is has a
function on its right-hand side:

> after :: CFLP cs m
>       => Nondet cs m (b -> c) -> Nondet cs m (a -> b)
>       -> Nondet cs m (a -> c)
> after f g = fun (\x cs -> withUnique $ \u -> apply f (apply g x cs u) cs)
>
> overApplication :: Assertion
> overApplication = assertResults comp [True]
>  where
>   comp = apply (after (fun not) (fun not)) true

The following test makes extensive use of higher-order features by
implementing the reverse function using `foldr`.

~~~ { .Haskell }
rev = flip (foldr (\x f l -> f (x:l)) id) []
~~~

> reverseWithFoldr :: Assertion
> reverseWithFoldr = assertResults comp [[True,False,False]]
>  where
>   comp = rev (false ^: false ^: true ^: nil)
>   rev  = flip (fun (foldr (fun (\x f l -> apply f (x ^: l))) (fun id))) nil
>
> flip :: CFLP cs m
>      => Nondet cs m (a -> b -> c) -> Nondet cs m b -> Nondet cs m a
>      -> Context cs -> ID -> Nondet cs m c
> flip f x y cs = withUnique $ \u -> apply (apply f y cs u) x cs
> 
> id :: Nondet cs m a -> Nondet cs m a
> id x = x

The following uses even more higher-order functions by implementing a
pointfree version of the above reverse function.

~~~ { .Haskell }
rev = flip (foldr (flip (flip ((.).(.)) (:))) id) []
~~~

-- > pointfreeReverse :: Assertion
-- > pointfreeReverse = assertResults comp [[True,False,False]]
-- >  where
-- >   comp cs = withUnique $ \u ->
-- >               apply (rev cs u) (false ^: false ^: true ^: nil) cs
-- > rev cs u = fun (flip (fun (foldr (fun (flip (fun (flip ((fun after `after` fun after) cs u) (fun (^:)))))) (fun id))) nil)

Currently, GHC (6.10.1) fails to compile the definition. The problem
seems to occur with many uses of `fun`:

-- > compileTimePerformanceBug
-- >   = fun id `after` fun id
-- >            `after` fun id
-- >            `after` fun id
-- >            `after` fun id
-- >            `after` fun id
-- >            `after` fun id

The following test converts primitive Haskell functions to
non-deterministic ones and applies them to non-deterministic values.

> functionConversion :: Assertion
> functionConversion = assertResults comp [False]
>  where
>   comp cs = withUnique $ \u ->
>              apply (foldr (fun after) (fun id)
>                       (nondet [P.not,P.not,P.not]) cs u)
>                true cs

