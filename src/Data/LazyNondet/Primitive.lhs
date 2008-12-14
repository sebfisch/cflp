% Primitive Generic Functions on Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> {-# LANGUAGE
>       FlexibleContexts
>   #-}
>
> module Data.LazyNondet.Primitive (
>
>   nondet, prim, groundNormalForm, partialNormalForm,
>
>   prim_eq
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
> import Unique
> import UniqSupply
>
> prim :: Data a => NormalForm -> a
> prim (Var u) = error $ "demand on logic variable " ++ show u
> prim (NormalForm con args) =
>   snd (gmapAccumT perkid args (fromConstr con))
>  where
>   perkid ts _ = (tail ts, prim (head ts))

The operation `prim` translates a normal form into a primitive Haskell
value. Free logic variables are translated into a call to `error` so
the result is a partial value if the argument contains logic
variables.

> generic :: Data a => a -> NormalForm
> generic x = NormalForm (toConstr x) (gmapQ generic x)
>
> nf2hnf :: Monad m => NormalForm -> Untyped cs m
> nf2hnf (Var _) = error $ "Primitive.nf2hnf: cannot convert logic variable"
> nf2hnf (NormalForm con args) = return (mkHNF con (map nf2hnf args))
>
> nondet :: (Monad m, Data a) => a -> Nondet cs m a
> nondet = Typed . nf2hnf . generic

We also provide a generic operation `nondet` to translate instances of
the `Data` class into non-deterministic data.

> groundNormalForm :: MonadSolve cs m m' => Nondet cs m a -> cs -> m' NormalForm
> groundNormalForm  = evalStateT . gnf . untyped
>
> partialNormalForm :: (MonadSolve cs m m', ChoiceStore cs)
>                   => Nondet cs m a -> cs -> m' NormalForm
> partialNormalForm = evalStateT . pnf . untyped

The `...NormalForm` functions evaluate a non-deterministic value and
lift all non-deterministic choices to the top level. The results are
deterministic values and can be converted into their Haskell
representation. Partial normal forms may contain unbound logic
variables while ground normal forms are data terms.

> gnf :: MonadSolve cs m m' => Untyped cs m -> StateT cs m' NormalForm
> gnf = nf (\_ _ -> Just ()) NormalForm mkVar
>
> mkVar :: ID -> a -> NormalForm
> mkVar (ID us) _ = Var (uniqFromSupply us)
>
> pnf :: (MonadSolve cs m m', ChoiceStore cs)
>     => Untyped cs m -> StateT cs m' NormalForm
> pnf x = nf lookupChoice ((return.).mkHNF) ((return.).FreeVar) x
>     >>= nf lookupChoice NormalForm mkVar

To compute ground normal forms, we ignore free variables and narrow
them to ground terms. To compute partial normal forms, we do not
narrow unbound variables and in a second phase bind those variables
that were bound after we have visited them. For example, when
computing the normal form of `let x free in (x,not x)` we don't know
that `x` will be bound in the result when we encounter it for the
first time.

> nf :: MonadSolve cs m m'
>    => (Unique -> cs -> Maybe a)
>    -> (Constr -> [nf] -> nf)
>    -> (ID -> Untyped cs m -> nf)
>    -> Untyped cs m -> StateT cs m' nf
> nf lkp cns fv x = do
>   hnf <- solve x
>   case hnf of
>     FreeVar u@(ID us) y ->
>       get >>= maybe (return (fv u y)) (const (nf lkp cns fv y))
>             . lkp (uniqFromSupply us)
>     Execute exe -> get >>= nf lkp cns fv . exe
>     Cons typ idx args -> do
>       nfs <- mapM (nf lkp cns fv) args
>       return (cns (indexConstr typ idx) nfs)

The `nf` function is used by all normal-form functions and performs al
the work.

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
