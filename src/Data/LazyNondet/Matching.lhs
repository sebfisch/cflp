% Pattern Matching of Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       RankNTypes,
>       TypeFamilies,
>       FlexibleContexts,
>       FlexibleInstances
>   #-}
>
> module Data.LazyNondet.Matching (
>
>   Match, ConsPatList(..), constructors, patterns,
>
>   withHNF, failure, caseOf, caseOf_
>
> ) where
>
> import Data.LazyNondet.Types
> import Data.LazyNondet.Generic
>
> import Control.Monad.State
> import Control.Monad.Update
>
> withHNF :: Update cs m m
>         => Nondet cs m a
>         -> (HeadNormalForm cs m -> Context cs -> Nondet cs m b)
>         -> Context cs -> Nondet cs m b
> withHNF x b (Context cs) = Typed (do
>   (hnf,cs') <- runStateT (updateState (untyped x)) cs
>   untyped (b hnf (Context cs')))

The `withHNF` operation can be used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value. An updated constraint store is passed to the computation of the
branch function. Collected constraints are kept attached to the
computed value by using an appropriate instance of `Update` that does
not eliminate them.

> class WithUntyped a
>  where
>   type C a
>   type M a :: * -> *
>   type T a
>
>   withUntyped :: a -> [Untyped (C a) (M a)] -> Nondet (C a) (M a) (T a)

We repeat the definition of the type class `With` because the current
implementation of GHC does not allow equality constraints in
super-class constraints. We would prefer to define this class as
follows:

    class (With [Untyped cs m] a, m ~ Mon [Untyped cs m] a) => WithUnique a
     where
      withUnique :: a -> [Untyped cs m] -> Nondet cs m (Typ [Untyped cs m] a)
      withUnique = with

So it is just a copy of the type class `With` where the argument type
is specialized to use the same monad.

> instance WithUntyped (Nondet cs m a)
>  where
>   type C (Nondet cs m a) = cs
>   type M (Nondet cs m a) = m
>   type T (Nondet cs m a) = a
>
>   withUntyped = const
>
> instance (WithUntyped a, cs ~ C a, m ~ M a)
>        => WithUntyped (Nondet cs m b -> a)
>  where
>   type C (Nondet cs m b -> a) = C a
>   type M (Nondet cs m b -> a) = M a
>   type T (Nondet cs m b -> a) = T a
>
>   withUntyped alt (x:xs) = withUntyped (alt (Typed x)) xs
>   withUntyped _ _ = error "LazyNondet.withUntyped: too few arguments"

These instances define the overloaded function `withUntyped` that has
all of the following types at the same time:

    withUntyped :: Nondet cs m a
                -> [Untyped cs m] -> Nondet cs m a

    withUntyped :: (Nondet cs m a -> Nondet cs m b)
                -> [Untyped cs m] -> Nondet cs m b

    withUntyped :: (Nondet cs m a -> Nondet cs m b -> Nondet cs m c)
                -> [Untyped cs m] -> Nondet cs m c
    ...

If the function given as first argument has n arguments, then the
application of `withUntyped` to this function consumes n elements of
the list of untyped values and yields the result of applying the given
function to typed versions of these values.

> newtype Match a cs m b
>   = Match { unMatch :: (Int, Context cs -> Branch cs m b) }
>
> type Branch cs m a = [Untyped cs m] -> Nondet cs m a
>
> match :: WithUntyped a
>       => Int -> (Context (C a) -> a) -> Match t (C a) (M a) (T a)
> match n alt = Match (n, withUntyped . alt)

The operation `match` is used to build destructor functions for
non-deterministic values that can be used with `caseOf`.

> failure :: MonadPlus m => Nondet cs m a
> failure = Typed mzero

Failure is just a type version of `mzero`.

> caseOf :: Update cs m m
>        => Nondet cs m a -> [Match a cs m b] -> Context cs -> Nondet cs m b
> caseOf x bs = caseOf_ x bs failure
>
> caseOf_ :: Update cs m m
>         => Nondet cs m a -> [Match a cs m b] -> Nondet cs m b
>         -> Context cs -> Nondet cs m b
> caseOf_ x bs def =
>   withHNF x $ \hnf cs ->
>   case hnf of
>     FreeVar _ y -> caseOf_ (Typed y) bs def cs
>     Delayed p res
>       | p cs      -> delayed p (\cs -> caseOf_ (Typed (res cs)) bs def cs)
>       | otherwise -> caseOf_ (Typed (res cs)) bs def cs
>     Cons label args ->
>       maybe def (\b -> b cs args) (lookup (index label) (map unMatch bs))
>     Lambda _ -> error "Data.LazyNondet.Matching.caseOf: cannot match lambda"

We provide operations `caseOf_` and `caseOf` (with and without a
default alternative) for more convenient pattern matching. The untyped
values are hidden so functional-logic code does not need to match on
the `Cons` constructor explicitly. However, using this combinator
causes an additional slowdown because of the list lookup. It remains
to be checked how big the slowdown of using `caseOf` is compared to
using `withHNF` directly.


Defining Constructor and Destructor Functions
=============================================

We provide combinators `constructors` and `destructors` that can be
used to define functions for constructing and matching
non-deterministic values.

> class MkCons a
>  where
>   type Ctx a :: *
>   type Mon a :: * -> *
>   type Res a :: *
>
>   mkCons :: ConsLabel -> [Untyped (Ctx a) (Mon a)] -> a
>
> instance Monad m => MkCons (Nondet cs m a)
>  where
>   type Ctx (Nondet cs m a) = cs
>   type Mon (Nondet cs m a) = m
>   type Res (Nondet cs m a) = a
>
>   mkCons l = Typed . return . Cons l . reverse
>
> instance (MkCons b, cs ~ Ctx b, m ~ Mon b) => MkCons (Nondet cs m a -> b)
>  where
>   type Ctx (Nondet cs m a -> b) = cs
>   type Mon (Nondet cs m a -> b) = m
>   type Res (Nondet cs m a -> b) = Res b
>
>   mkCons l xs x = mkCons l (untyped x:xs)
>
> infixr 0 :!
>
> data ConsPatList a b = a :! b
>
> class ConsList a
>  where
>   type CData a
>
>   consList :: [ConsLabel] -> a
>
> instance ConsList ()
>  where
>   type CData () = ()
>   consList _ = ()
>
> instance (MkCons a, ConsList b) => ConsList (ConsPatList a b)
>  where
>   type CData (ConsPatList a b) = Res a
>
>   consList (l:ls) = mkCons l [] :! consList ls
>   consList _ = error "consList: insufficient cons labels"
>
> constructors :: (ConsList a, Generic (CData a)) => a
> constructors = cs
>  where cs = consList (consLabels (undefined `asCDataOf` cs))
>
> asCDataOf :: ConsList a => CData a -> a -> CData a
> asCDataOf = const
>
> class PatternList a
>  where
>   type PData a
>
>   patternList :: [ConsLabel] -> a
>
> instance PatternList ()
>  where
>   type PData () = ()
>   patternList _ = ()
>
> instance (WithUntyped a, PatternList p, cs ~ C a, m ~ M a, b ~ T a)
>       => PatternList (ConsPatList ((Context cs -> a) -> Match t cs m b) p)
>  where
>   type PData (ConsPatList ((Context cs -> a) -> Match t cs m b) p) = t
>
>   patternList (l:ls) = match (index l) :! patternList ls
>   patternList _ = error "patternList: insufficient cons labels"
>
> patterns :: (PatternList a, Generic (PData a)) => a
> patterns = cs
>  where cs = patternList (consLabels (undefined `asPDataOf` cs))
>
> asPDataOf :: PatternList a => PData a -> a -> PData a
> asPDataOf = const

