% Primitive Generic Functions on Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.Primitive (
>
>   nondet, normalForm, prim_eq
>
> ) where
>
> import Data.Data
> import Data.Generics.Twins
> import Data.LazyNondet.Types
>
> import Control.Monad.State
> import Control.Monad.Constraint
> import Control.Monad.Constraint.Choice
>
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
>     FreeVar _ y -> nf y
>     Execute exe -> get >>= nf . exe
>     Cons typ idx args -> do
>       nfs <- mapM nf args
>       return (NormalForm (indexConstr typ idx) nfs)

The `normalForm` function evaluates a non-deterministic value and
lifts all non-deterministic choices to the top level. The results are
deterministic values and can be converted into their Haskell
representation.

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
