% Primitive Generic Functions on Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> module CFLP.Data.Primitive (
>
>   nondet, groundNormalForm, partialNormalForm,
>
>   prim_eq
>
> ) where
>
> import Data.Supply
>
> import Control.Monad.State
>
> import CFLP.Data.Types
> import CFLP.Data.Generic
>
> import CFLP.Control.Monad.Update
> import CFLP.Control.Strategy

We provide a generic operation `nondet` to translate instances of
`Generic` into non-deterministic data.

> nondet :: (Monad m, Update cs m m, Generic a) => a -> Nondet cs m a
> nondet = Typed . return . nf2hnf . generic
>
> nf2hnf :: (Monad m, Update cs m m) => NormalForm -> HeadNormalForm cs m
> nf2hnf (Var _) = error "Primitive.nf2hnf: cannot convert logic variable"
> nf2hnf (Data label args) = Cons label (map (return . nf2hnf) args)
> nf2hnf (Fun f) = Lambda (\x _ _ -> liftM (nf2hnf . f) $ gnf x)
>  where gnf x = groundNormalForm (Typed x) $
>                  error "Primitive.nf2hnf: primitive function uses context"

The `...NormalForm` functions evaluate a non-deterministic value and
lift all non-deterministic choices to the top level. The results are
deterministic values and can be converted into their Haskell
representation. Partial normal forms may contain unbound logic
variables while ground normal forms are data terms.

> groundNormalForm :: (Monad s, Monad m, Update c s m)
>                  => Nondet c s a -> Context c -> m NormalForm
> groundNormalForm x (Context cs) = evalStateT (gnf (untyped x)) cs
>
> partialNormalForm :: (Monad s, Strategy c s, Monad m, Update c s m)
>                   => Nondet c s a -> Context c -> m NormalForm
> partialNormalForm x (Context cs) = evalStateT (pnf (untyped x)) cs

To compute ground normal forms, we ignore free variables and narrow
them to ground terms. To compute partial normal forms, we do not
narrow unbound variables and in a second phase bind those variables
that were bound after we have visited them. For example, when
computing the normal form of `let x free in (x,not x)` we don't know
that `x` will be bound in the result when we encounter it for the
first time.

> gnf :: (Monad s, Monad m, Update c s m)
>     => Untyped c s -> StateT c m NormalForm
> gnf = nf (\_ _ -> return True) Data mkVar Fun
>
> mkVar :: ID -> a -> NormalForm
> mkVar (ID us) _ = Var (supplyValue us)
>
> pnf :: (Monad s, Strategy c s, Monad m, Update c s m)
>     => Untyped c s -> StateT c m NormalForm
> pnf x
>    = nf isNarrowed ((return.).Cons) ((return.).FreeVar) (return.Lambda) x
>  >>= nf isNarrowed Data mkVar Fun

The `nf` function is used by all normal-form functions and performs
all the work.

> nf :: (Monad m, Update c s m)
>    => (c -> Int -> s Bool)
>    -> (ConsLabel -> [nf] -> nf)
>    -> (ID -> Untyped c s -> nf)
>    -> (b -> nf)
>    -> Untyped c s -> StateT c m nf
> nf isn cns fv fun x = do
>   hnf <- updateState x
>   case hnf of
>     FreeVar u@(ID us) y -> do
>       narrowed <- get >>= updateState . (`isn` supplyValue us)
>       if narrowed
>        then nf isn cns fv fun y
>        else return (fv u y)
>     Delayed _ resume -> get >>= nf isn cns fv fun . resume . Context
>     Cons label args -> do
>       nfs <- mapM (nf isn cns fv fun) args
>       return (cns label nfs)
>     Lambda _ -> return . fun $ error "Data.LazyNondet.Primitive.nf: function"

We provide a generic comparison function for untyped non-deterministic
data that is used to define a typed equality test in the
`Data.LazyNondet.Types.Bool` module.

> prim_eq :: (Monad m, Update cs m m)
>         => Untyped cs m -> Untyped cs m -> StateT cs m Bool
> prim_eq x y = do
>   Cons lx xs <- solveCons x
>   Cons ly ys <- solveCons y
>   if index lx == index ly then all_eq xs ys else return False
>  where
>   all_eq [] [] = return True
>   all_eq (v:vs) (w:ws) = do
>     eq <- prim_eq v w
>     if eq then all_eq vs ws else return False
>   all_eq _ _ = return False

The function `solveCons` is like `solve` but always yields a
constructor-rooted term, i.e., no free variable or delayed
computation.

> solveCons :: (Monad m, Update cs m m)
>           => Untyped cs m -> StateT cs m (HeadNormalForm cs m)
> solveCons x = do
>   hnf <- updateState x
>   case hnf of
>     FreeVar _ y -> solveCons y
>     Delayed _ res -> get >>= solveCons . res . Context
>     Lambda _ -> error "Data.LazyNondet.Primitive.solveCons: matched lambda"
>     _ -> return hnf

