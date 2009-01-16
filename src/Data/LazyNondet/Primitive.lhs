% Primitive Generic Functions on Lazy Non-Deterministic Data
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

> module Data.LazyNondet.Primitive (
>
>   nondet, groundNormalForm, partialNormalForm,
>
>   prim_eq
>
> ) where
>
> import Data.LazyNondet.Types
> import Data.LazyNondet.Generic
>
> import Control.Monad.State
> import Control.Monad.Update
>
> import Control.Constraint.Choice
>
> import Data.Supply

We provide a generic operation `nondet` to translate instances of
`Generic` into non-deterministic data.

> nondet :: (Update cs m m, Generic a) => a -> Nondet cs m a
> nondet = Typed . return . nf2hnf . generic
>
> nf2hnf :: Update cs m m => NormalForm -> HeadNormalForm cs m
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

> groundNormalForm :: Update cs m m'
>                  => Nondet cs m a -> Context cs -> m' NormalForm
> groundNormalForm x (Context cs) = evalStateT (gnf (untyped x)) cs
>
> partialNormalForm :: (Update cs m m', ChoiceStore cs)
>                   => Nondet cs m a -> Context cs -> m' NormalForm
> partialNormalForm x (Context cs) = evalStateT (pnf (untyped x)) cs

To compute ground normal forms, we ignore free variables and narrow
them to ground terms. To compute partial normal forms, we do not
narrow unbound variables and in a second phase bind those variables
that were bound after we have visited them. For example, when
computing the normal form of `let x free in (x,not x)` we don't know
that `x` will be bound in the result when we encounter it for the
first time.

> gnf :: Update cs m m' => Untyped cs m -> StateT cs m' NormalForm
> gnf = nf (\_ _ -> Just ()) Data mkVar Fun
>
> mkVar :: ID -> a -> NormalForm
> mkVar (ID us) _ = Var (supplyValue us)
>
> pnf :: (Update cs m m', ChoiceStore cs)
>     => Untyped cs m -> StateT cs m' NormalForm
> pnf x
>    = nf lookupChoice ((return.).Cons) ((return.).FreeVar) (return.Lambda) x
>  >>= nf lookupChoice Data mkVar Fun

The `nf` function is used by all normal-form functions and performs
all the work.

> nf :: Update cs m m'
>    => (Int -> cs -> Maybe a)
>    -> (ConsLabel -> [nf] -> nf)
>    -> (ID -> Untyped cs m -> nf)
>    -> (b -> nf)
>    -> Untyped cs m -> StateT cs m' nf
> nf lkp cns fv fun x = do
>   hnf <- updateState x
>   case hnf of
>     FreeVar u@(ID us) y ->
>       get >>= maybe (return (fv u y)) (const (nf lkp cns fv fun y))
>             . lkp (supplyValue us)
>     Delayed _ resume -> get >>= nf lkp cns fv fun . resume . Context
>     Cons label args -> do
>       nfs <- mapM (nf lkp cns fv fun) args
>       return (cns label nfs)
>     Lambda _ -> return . fun $ error "Data.LazyNondet.Primitive.nf: function"

We provide a generic comparison function for untyped non-deterministic
data that is used to define a typed equality test in the
`Data.LazyNondet.Types.Bool` module.

> prim_eq :: Update cs m m
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

> solveCons :: Update cs m m
>           => Untyped cs m -> StateT cs m (HeadNormalForm cs m)
> solveCons x = do
>   hnf <- updateState x
>   case hnf of
>     FreeVar _ y -> solveCons y
>     Delayed _ res -> get >>= solveCons . res . Context
>     Lambda _ -> error "Data.LazyNondet.Primitive.solveCons: matched lambda"
>     _ -> return hnf

