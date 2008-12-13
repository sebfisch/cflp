% Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides a datatype with operations for lazy
non-deterministic programming.

> {-# LANGUAGE
>       ExistentialQuantification,
>       FunctionalDependencies,
>       MultiParamTypeClasses,
>       FlexibleInstances,
>       FlexibleContexts,
>       TypeFamilies,
>       RankNTypes
>   #-}
>
> module Data.LazyNondet (
>
>   NormalForm, HeadNormalForm(..), mkHNF, Nondet(..),
>
>   ID, initID, withUnique,
>
>   Narrow(..), unknown, failure, oneOf, withHNF, caseOf, caseOf_, Match,
>
>   Data, nondet, normalForm,
>
>   ConsRep(..), cons, match,
>
>   prim_eq
>
> ) where
>
> import Data.Data
> import Data.Generics.Twins ( gmapAccumT )
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
> import UniqSupply

We borrow unique identifiers from the package `ghc` which is hidden by
default.

> data NormalForm = NormalForm Constr [NormalForm]
>  deriving Show

The normal form of data is represented by the type `NormalForm` which
defines a tree of constructors. The type `Constr` is a representation
of constructors defined in the `Data.Generics` package. With generic
programming we can convert between Haskell data types and the
`NormalForm` type.

> data HeadNormalForm cs m
>   = Cons DataType ConIndex [Untyped cs m]
>   | forall a . Narrow cs a => Unknown (NarrowPolicy cs a) ID (Nondet cs m a)
>
> type Untyped cs m = m (HeadNormalForm cs m)

Data in lazy functional-logic programs is evaluated on demand. The
evaluation of arguments of a constructor may lead to different
non-deterministic results. Hence, we use a monad around every
constructor in the head-normal form of a value.

> newtype Nondet cs m a = Typed { untyped :: Untyped cs m }

Untyped non-deterministic data can be phantom typed in order to define
logic variables by overloading. The phantom type must be the Haskell
data type that should be used for conversion into primitive data.

> mkHNF :: Constr -> [Untyped cs m] -> HeadNormalForm cs m
> mkHNF c args = Cons (constrType c) (constrIndex c) args

In head-normal forms we split the constructor representation into a
representation of the data type and the index of the constructor, to
enable pattern matching on the index.

Free (logic) variables are represented by `Unknown p u x` where `u` is a
uniqe identifier and `x` which represents the result of narrowing the
variable according to the constraint store passed to the operation
that creates the variable. 

The variable `p` is a NrrowingPolicy` that specifies whether the
variable should be

 * narrowed whenever it is demanded according the current constraint
   store or

 * narrowed only on creation and shared on every demand.

> data NarrowPolicy cs a = OnDemand | OnCreation

Using `OnDemand` can avoid unnessesary branching when accessing a
variable with an updated constraint store. Using `OnCreation` will
avoid the reexecution of a non-deterministic generator, which is
especially useful if it does not consider the constraint store.

> class Narrow cs a
>  where
>   narrowPolicy :: NarrowPolicy cs a
>   narrowPolicy = OnCreation
>
>   narrow :: MonadConstr Choice m => cs -> ID -> Nondet cs m a

Logic variables of type `a` can be narrowed to head-normal form if
there is an instance of the type class `Narrow`. A constraint store
may be used to find the possible results which are returned in a monad
that supports choices. Usually, `narrow` will be implemented as a
non-deterministic generator using `oneOf`, but for specific types
different strategies may be implemented.

The default policy is to narrow on creation and share the results
narrowed on creation. Instances of `Narrow` that don't use the
constraint store but simply define a non-deterministic generator,
hence, don't need to specify a `NarrowPolicy`.

 > narrowHNF :: Narrow cs a => HeadNormalForm cs m -> cs -> Nondet cs m a

 > narrowHNF (Unknown OnDemand   u x) cs = narrow cs u
 > narrowHNF (Unknown OnCreation _ x) _  = x
 > narrowHNF x _ = x

The function `narrowHNF` narrows logic variables according to their
policy and has no effect on constructor-rooted values.

Threading Unique Identifiers
----------------------------

Non-deterministic computations need a supply of unique identifiers in
order to constrain shared choices.

> newtype ID = ID UniqSupply
>
> initID :: IO ID
> initID = liftM ID $ mkSplitUniqSupply 'x'
>
> class With x a
>  where
>   type CSt x a
>   type Mon x a :: * -> *
>   type Typ x a
>
>   with :: a -> x -> Nondet (CSt x a) (Mon x a) (Typ x a)
>
> instance With x (Nondet cs m a)
>  where
>   type CSt x (Nondet cs m a) = cs
>   type Mon x (Nondet cs m a) = m
>   type Typ x (Nondet cs m a) = a
>
>   with = const
>
> instance With ID a => With ID (ID -> a)
>  where
>   type CSt ID (ID -> a) = CSt ID a
>   type Mon ID (ID -> a) = Mon ID a
>   type Typ ID (ID -> a) = Typ ID a
>
>   with f (ID us) = withUnique (f (ID vs)) (ID ws)
>    where (vs,ws) = splitUniqSupply us
>
> withUnique :: With ID a => a -> ID -> Nondet (CSt ID a) (Mon ID a) (Typ ID a)
> withUnique = with

We provide an overloaded operation `withUnique` to simplify the
distribution of unique identifiers when defining possibly
non-deterministic operations. Non-deterministic operations have an
additional argument for unique identifiers. The operation `withUnique`
allows to consume an arbitrary number of unique identifiers hiding
their generation. Conceptually, it has all of the following types at
the same time:

    Nondet m a -> ID -> Nondet m a
    (ID -> Nondet m a) -> ID -> Nondet m a
    (ID -> ID -> Nondet m a) -> ID -> Nondet m a
    (ID -> ID -> ID -> Nondet m a) -> ID -> Nondet m a
    ...

We make use of type families because GHC considers equivalent
definitions with functional dependencies illegal due to the overly
restrictive "coverage condition".

Combinators for Functional-Logic Programming
--------------------------------------------

> unknown :: (MonadConstr Choice m, Narrow cs a) => cs -> ID -> Nondet cs m a
> unknown cs u = x
>  where
>   x = Typed (return (Unknown narrowPolicy u (narrow cs u `withTypeOf` x)))
>
> withTypeOf :: a -> a -> a
> x `withTypeOf` _ = x

The application of `unknown` to a constraint store and a unique
identifier represents a logic variable of an arbitrary type. The
definition uses the helper function `withTypeOf` in order to constrain
the type of a dummy argument.

> oneOf :: MonadConstr Choice m => [Nondet cs m a] -> ID -> Nondet cs m a
> oneOf xs (ID us) = Typed (choice (uniqFromSupply us) (map untyped xs))

The operation `oneOf` takes a list of non-deterministic values and
returns a non-deterministic value that yields one of the elements in
the given list.

> failure :: MonadPlus m => Nondet cs m a
> failure = Typed mzero

A failing computation could be defined using `oneOf`, but we provide a
special combinator that does not need a supply of unique identifiers.

> withHNF :: (Monad m, MonadSolve cs m m)
>         => Nondet cs m a
>         -> (HeadNormalForm cs m -> cs -> Nondet cs m b)
>         -> cs -> Nondet cs m b
> withHNF x b cs = Typed (do
>   (hnf,cs') <- runStateT (solve (untyped x)) cs
>   untyped (b hnf cs'))

The `withHNF` operation can be used for pattern matching and solves
constraints associated to the head constructor of a non-deterministic
value. An updated constraint store is passed to the computation of the
branch function. Collected constraints are kept attached to the
computed value by using an appropriate instance of `MonadSolve` that
does not eliminate them.

> caseOf :: (MonadSolve cs m m, MonadConstr Choice m, Narrow cs a)
>        => Nondet cs m a -> [Match cs m b] -> cs -> Nondet cs m b
> caseOf x bs = caseOf_ x bs failure
>
> caseOf_ :: (MonadSolve cs m m, MonadConstr Choice m, Narrow cs a)
>         => Nondet cs m a -> [Match cs m b] -> Nondet cs m b
>         -> cs -> Nondet cs m b
> caseOf_ x bs def =
>   withHNF x $ \hnf cs ->
>   case hnf of
>     Unknown OnCreation _ y -> caseOf_ y bs def cs
>     Unknown OnDemand   u y -> caseOf_ (narrow cs u `withTypeOf` y) bs def cs
>     Cons _ idx args ->
>       maybe def (\b -> branch (b cs) args) (lookup idx (map unMatch bs))
>
> newtype Match cs m a = Match { unMatch :: (ConIndex, cs -> Branch cs m a) }
> data Branch cs m a =
>   forall t . (WithUntyped t, cs ~ C t, m ~ M t, a ~ T t) => Branch t
>
> branch :: Branch cs m a -> [Untyped cs m] -> Nondet cs m a
> branch (Branch alt) = withUntyped alt

We provide operations `caseOf` and `caseOf` (with and without a
default alternative) for more convenient pattern matching. The untyped
values are hidden so functional-logic code does not need to match on
the `Cons` constructor explicitly. However, using this combinator
causes an additional slowdown because of the list lookup. It remains
to be checked how big the slowdown of using `caseOf` is compared to
using `withHNF` directly.

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

Converting Between Primitive and Non-Deterministic Data
-------------------------------------------------------

> prim :: Data a => NormalForm -> a
> prim (NormalForm con args) =
>   snd (gmapAccumT perkid args (fromConstr con))
>  where
>   perkid ts _ = (tail ts, prim (head ts))
>
> generic :: Data a => a -> NormalForm
> generic x = NormalForm (toConstr x) (gmapQ generic x)
>
> nf2hnf :: Monad m => NormalForm -> Untyped cs m
> nf2hnf (NormalForm con args) = return (mkHNF con (map nf2hnf args))
>
> nondet :: (Monad m, Data a) => a -> Nondet cs m a
> nondet = Typed . nf2hnf . generic

We provide generic operations to convert between instances of the
`Data` class and non-deterministic data.

> normalForm :: (MonadSolve cs m m', MonadConstr Choice m, Data a)
>            => Nondet cs m a -> cs -> m' a
> normalForm x cs = liftM prim $ evalStateT (nf (untyped x)) cs
>
> nf :: (MonadSolve cs m m', MonadConstr Choice m)
>    => Untyped cs m -> StateT cs m' NormalForm
> nf x = do
>   hnf <- solve x
>   case hnf of
>     Unknown OnCreation _ y -> nf (untyped y)
>     Unknown OnDemand   u y -> do
>       cs <- get
>       nf (untyped (narrow cs u `withTypeOf` y) )
>     Cons typ idx args -> do
>       nfs <- mapM nf args
>       return (NormalForm (indexConstr typ idx) nfs)

The `normalForm` function evaluates a non-deterministic value and
lifts all non-deterministic choices to the top level. The results are
deterministic values and can be converted into their Haskell
representation.

Syntactic Sugar for Datatype Declarations
-----------------------------------------

> class MkCons cs m a b | b -> m, b -> cs
>  where
>   mkCons :: a -> [Untyped cs m] -> b
>
> instance (Monad m, Data a) => MkCons cs m a (Nondet cs m t)
>  where
>   mkCons c args = Typed (return (mkHNF (toConstr c) (reverse args)))
>
> instance MkCons cs m b c => MkCons cs m (a -> b) (Nondet cs m t -> c)
>  where
>   mkCons c xs x = mkCons (c undefined) (untyped x:xs)
>
> cons :: MkCons cs m a b => a -> b
> cons c = mkCons c []

The overloaded operation `constr` takes a Haskell constructor and yields
a corresponding constructor function for non-deterministic values.

> match :: (ConsRep a, WithUntyped b)
>       => a -> (C b -> b) -> Match (C b) (M b) (T b)
> match c alt = Match (constrIndex (consRep c), Branch . alt)

The operation `decons` is used to build destructor functions for
non-deterministic values that can be used with `caseOf`.

> class ConsRep a
>  where
>   consRep :: a -> Constr
>
> instance ConsRep b => ConsRep (a -> b)
>  where
>   consRep c = consRep (c undefined)

We provide an overloaded operation `consRep` that yields a `Constr`
representation for a constructor rather than for a constructed value
like `Data.Data.toConstr` does. We do not provide the base instance

    instance Data a => ConsRep a
     where
      consRep = toConstr

because this would require to allow undecidable instances. As a
consequence, specialized base instances need to be defined for every
used datatype. See `Data.LazyNondet.List` for an example of how to get
the representation of polymorphic constructors and destructors.

Primitive Generic Functions
---------------------------

> prim_eq :: MonadSolve cs m m
>         => Untyped cs m -> Untyped cs m -> StateT cs m Bool
> prim_eq x y = do
>   Cons _ ix xs <- solve x
>   Cons _ iy ys <- solve y
>   if ix==iy then all_eq xs ys else return False
>  where
>   all_eq [] [] = return True
>   all_eq (v:vs) (w:ws) = do
>     eq <- prim_eq v w
>     if eq then all_eq vs ws else return False
>   all_eq _ _ = return False

We provide a generic comparison function for untyped non-deterministic
data that is used to define a typed equality test in the
`Data.LazyNondet.Bool` module.

`Show` Instances
----------------

> instance Show (HeadNormalForm cs [])
>  where
>   show (Unknown _ (ID u) _) = show (uniqFromSupply u)
>   show (Cons typ idx args) 
>     | null args = show con
>     | otherwise = unwords (("("++show con):map show args++[")"])
>    where con = indexConstr typ idx
>
> instance Show (Nondet cs [] a)
>  where
>   show = show . untyped
>
> instance Show (Nondet cs (ConstrT cs []) a)
>  where
>   show = show . untyped
>
> instance Show (HeadNormalForm cs (ConstrT cs []))
>  where
>   show (Unknown _ (ID u) _) = show (uniqFromSupply u)
>   show (Cons typ idx [])    = show (indexConstr typ idx)
>   show (Cons typ idx args)  =
>     "("++show (indexConstr typ idx)++" "++unwords (map show args)++")" 

To simplify debugging, we provide `Show` instances for head-normal
forms and non-deterministic values.

