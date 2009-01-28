% Generic Operations on Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides generic operations on the datatypes used
internally for constraint functional-logic programming. We cannot use
the `Data.Data` class, because we also want to handle functions.

`Typeable` or `DrIFT` may be applicable, however, to derive some of
the instances for classes defined in this module.

> {-# LANGUAGE TypeFamilies #-}
>
> module CFLP.Data.Generic (
>
>   Generic(..), GenericOps, generic, primitive, consLabels,
>
>   ApplyCons(..), Decons, (!), cons
>
>  ) where
>
> import Data.Maybe
>
> import CFLP.Data.Types

Here is a record with generic operations:

> data GenericOps a = GenericOps {

The operation `gen` converts a value of type `a` into the generic
normal-form representation.

>   gen :: a -> Maybe NormalForm ,

The operation `prim` converts a normal form into a primitive Haskell
value of type `a`.

>   prim :: NormalForm -> Maybe a ,

The field `labels` stores a list of `ConsLabels` corresponding to the
constructors of a datatype.

>   labels :: [ConsLabel] }

The generic operations `gen` and `prim` return optional
results. However, failure is only used internally and there are
wrapper functions that always succeed:

> generic :: Generic a => a -> NormalForm
> generic = fromJust . gen genericOps
>
> primitive :: Generic a => NormalForm -> a
> primitive = fromJust . prim genericOps

The operation `consLabels` yields the list of constructors
corresponding to a datatype `a`.

> consLabels :: Generic a => a -> [ConsLabel]
> consLabels x = labels (genericOps `forTypeOf` x)
>
> forTypeOf :: GenericOps a -> a -> GenericOps a
> forTypeOf = const

The operation `genericOps` is defined in the type class `Generic`:

> class Generic a
>  where
>   genericOps :: GenericOps a
>   genericOps = constr 0
>
>   constr :: Int -> GenericOps a
>   constr _ = error "Generic.constr: not implemented"

Primitive Haskell types that should be convertible to be used in
constraint functional-logic programs need to be instances of
`Generic`.

The operation `genericOps` has a default implementation in terms of
`constr` to simplify the definition of instances for *data*types. The
instance for function types defines `genericOps` directly:

> instance (Generic a, Generic b) => Generic (a -> b)
>  where
>   genericOps = GenericOps {
>     gen    = \ f       -> Just (Fun (generic   . f . primitive)) ,
>     prim   = \ (Fun f) -> Just      (primitive . f . generic   ) ,
>     labels = [] }


Defining Instances
==================

We provide combinators to simplify the definition of `Generic`
instances for datatypes. For example, the instance for booleans looks
like this:

> instance Generic Bool
>  where
>   constr = cons "False" False dFalse ! cons "True" True dTrue

The arguments `dFalse` and `dTrue` are deconstructors for the
corresponding constructors:

> type Decons a = ([NormalForm] -> NormalForm) -> Result a -> Maybe NormalForm

The type `Result a` used in the type of deconstructors is associated
to the type class `ApplyCons`. 

> class ApplyCons a
>  where
>   type Result a
>   applyCons :: a -> [NormalForm] -> Result a

We can use `applyCons` to apply constructors of arbitrary arity:

> instance (Generic a, ApplyCons b) => ApplyCons (a -> b)
>  where
>   type Result (a -> b) = Result b
>
>   applyCons c (x:xs) = applyCons (c (primitive x)) xs
>   applyCons _ _ = error "applyCons: insufficient arguments"

We need an instance of `ApplyCons` for booleans in order to define the
`Generic` instance using our combinators. Instantiating `ApplyCons` is
easy, however. The definitions are always the same: `Result a = a` and
`applyCons = const`.

> instance ApplyCons Bool
>  where
>   type Result Bool = Bool
>   applyCons = const

Deconstructors are also defined mechanically:

> dFalse, dTrue :: Decons Bool
> dFalse c False = Just (c [])
> dFalse _ _     = Nothing
> dTrue  c True  = Just (c [])
> dTrue  _ _     = Nothing

We can even define an instance of integers:

> instance ApplyCons Int where type Result Int = Int; applyCons = const
> instance Generic Int
>  where constr = foldr1 (!) . map intCons $ interleaved [0..] [-1,-2..]
>
> interleaved :: [a] -> [a] -> [a]
> interleaved []     ys = ys
> interleaved (x:xs) ys = x : interleaved ys xs
>
> intCons :: Int -> Int -> GenericOps Int
> intCons n = cons (show n) n (\c m -> if n==m then Just (c []) else Nothing)

Combinators
-----------

The combinator `(!)` used to enumerate the constructors of a datatype
combines records with generic operations. The integer argument is used
to label the different constructors.

> infixr 0 !
> (!) :: (Int -> GenericOps a) -> (Int -> GenericOps a) -> Int -> GenericOps a
> (c1!c2) n =
>   GenericOps {
>     gen    = \x -> maybe (gen  genOps2 x) Just (gen  genOps1 x) ,
>     prim   = \x -> maybe (prim genOps2 x) Just (prim genOps1 x) ,
>     labels = labels genOps1 ++ labels genOps2 }
>  where genOps1 = c1 n; genOps2 = c2 (n+1)

We rely on `(!)` to be right associative: if `(!)` takes the result of
a different call to `(!)` as left argument then the distributed
numbers won't be distinct!

Finally, we define the `cons` combinator that takes constructors and
corresponding destructors.

> cons :: ApplyCons a => String -> a -> Decons a -> Int -> GenericOps (Result a)
> cons s c d n =
>   GenericOps {
>     gen    = d (Data (ConsLabel n s)),
>     prim   = \ (Data l xs) ->
>                  if n == index l then Just (applyCons c xs) else Nothing,
>     labels = [ConsLabel n s]
>    }

In order to convert a value to the generic normal-form representation
we can use the destructor function. To convert in the other direction
we check whether the label of the constructor equals the label of the
converter and, if it does, we use `applyCons` to apply the
corresponding constructor.


