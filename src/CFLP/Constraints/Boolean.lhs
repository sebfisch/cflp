% Boolean Constraints for CFLP
% Sebastian Fischer (sebf@informatik.uni-kiel.de)

This module provides boolean constraints for constraint
functional-logic programming.

> {-# LANGUAGE
>       GeneralizedNewtypeDeriving,
>       NoMonomorphismRestriction,
>       MultiParamTypeClasses,
>       OverlappingInstances,
>       FlexibleInstances,
>       FlexibleContexts,
>       NoMonoPatBinds,
>       TypeFamilies
>   #-}
>
> module CFLP.Constraints.Boolean (
>
>   Boolean, yes, no, neg, (.&&.), (.||.),
>
>   BooleanSolver(..), SatCtx, Sat, satSolving,
>
>   ifThen, ifThenElse, booleanToBool
>
>  ) where
>
> import Control.Monad
>
> import CFLP
> import CFLP.Control.Strategy
>
> import CFLP.Control.Monad.Update
>
> import CFLP.Data.Types
>   ( HeadNormalForm(..), Nondet(..), Context(..), label, joinNondet )
> import CFLP.Data.Primitive
>
> import CFLP.Types.Bool
>
> import Data.Boolean.SatSolver

Generic Creation of Boolean Formulas
====================================

We make the type of boolean formulas an instance of `ApplyCons` and
`Generic` in order to be able to define boolean formulas in CFLP
programs.

> instance ApplyCons Boolean
>   where
>    type Result Boolean = Boolean
>    applyCons = const
>
> instance Generic Boolean
>  where
>   constr = cons "BVAR"  Var    dVar
>          ! cons "TRUE"  Yes    dYes
>          ! cons "FALSE" No     dNo
>          ! cons "NOT"   Not    dNot
>          ! cons "AND"   (:&&:) dAnd
>          ! cons "OR"    (:||:) dOr
>
> dVar, dYes, dNo, dNot, dAnd, dOr :: Decons Boolean
>
> dVar c (Var n) = Just (c [generic n])
> dVar _ _       = Nothing
>
> dYes c Yes = Just (c [])
> dYes _ _   = Nothing
>
> dNo c No = Just (c [])
> dNo _ _  = Nothing
>
> dNot c (Not x) = Just (c [generic x])
> dNot _ _       = Nothing
>
> dAnd c (x:&&:y) = Just (c [generic x, generic y])
> dAnd _ _        = Nothing
>
> dOr c (x:||:y) = Just (c [generic x, generic y])
> dOr _ _        = Nothing

We define functions for constructing boolean formulas, but none for
pattern matching.

> infixr 3 .&&.
> infixr 2 .||.
>
> var            :: Monad m => Nondet c m Int -> Nondet c m Boolean
> yes, no        :: Monad m => Nondet c m Boolean
> neg            :: Monad m => Nondet c m Boolean -> Nondet c m Boolean
> (.&&.), (.||.) :: Monad m => Nondet c m Boolean -> Nondet c m Boolean
>                           -> Nondet c m Boolean
>
> var :! yes :! no :! neg :! (.&&.) :! (.||.) :! () = constructors


Extending Computations with SAT Solving
==============================================

An evaluation context that can satisfy boolean formulas is an instance
of the following type class.

> class BooleanSolver c
>  where
>   lookupBoolean :: Int -> c -> Maybe Bool
>   assertBoolean :: MonadPlus m => c -> Boolean -> c -> m c

A transformed boolean solver is still a boolean solver.

> instance (BooleanSolver c, Transformer t) => BooleanSolver (t c)
>  where
>   lookupBoolean n = lookupBoolean n . project
>   assertBoolean _ = inside . assertBoolean undefined

We define a context transformer that adds SAT-solving capabilities to
an arbitrary context.

> data SatCtx c = SatCtx SatSolver c
>
> instance Transformer SatCtx
>  where
>   project (SatCtx _ c) = c
>   replace (SatCtx s _) = SatCtx s

A context of type `SatCtx c` is always a boolean solver.

> instance BooleanSolver (SatCtx c)
>  where
>   lookupBoolean   n (SatCtx s _) = lookupVar n s
>   assertBoolean _ b (SatCtx s c) = liftM (flip SatCtx c) (assertTrue b s)

It is also solvable.

> instance Solvable c => Solvable (SatCtx c)
>  where
>   solvable (SatCtx s c) = isSolvable s && solvable c
>   bindVars (SatCtx s c) = liftM2 SatCtx (solve s) (bindVars c)

We define a strategy transformer to create SAT solving strategies.

> newtype Sat s a = Sat { fromSat :: s a }
>  deriving (Monad, MonadPlus, Enumerable)
>
> type instance Ctx (Sat s) = SatCtx (Ctx s)
> type instance Res (Sat s) = Sat (Res s)
>
> instance BooleanSolver c => StrategyT c Sat
>  where
>   liftStrategy _ = Sat
>   baseStrategy _ = fromSat
>
>   alterNarrowed c n b = maybe b (const (return True)) (lookupBoolean n c)

The context of a sat solving strategy is initialized with a new sat
solver.

> satSolving :: Monad s => s c -> Sat s (SatCtx c)
> satSolving = Sat . liftM (SatCtx newSatSolver)


Narrowing and Guards
====================

We provide an instance of `Narrow` for booleans in order to be able to
create logic boolean variables. We can create such variables if the
evaluation context is a boolean solver.

> instance BooleanSolver c => Narrow c Boolean
>  where
>   narrow (Context c) u =
>     let v = label u
>      in maybe (var (nondet v))
>               (\b -> if b then yes else no)
>               (lookupBoolean v c)

The function `ifThen` implements a guard for boolean formulas.

> ifThen :: (CFLP s, BooleanSolver (Ctx s))
>        => Data s Boolean -> Data s a -> Context (Ctx s) -> Data s a
> ifThen x y = withPrim x $ \b c ->
>   joinNondet (do update (assertBoolean c b); return y)

We also provide `ifThenElse`.

> ifThenElse :: (CFLP s, BooleanSolver (Ctx s))
>            => Data s Boolean -> Data s a -> Data s a
>            -> Context (Ctx s) -> Data s a
> ifThenElse x y z = withPrim x $ \b c ->
>   joinNondet ((do update (assertBoolean c b); return y)
>               `mplus` -- don't need choice constraints here!
>               (do update (assertBoolean c (Not b)); return z))

Boolean constraints can be converted to boolean data terms.

> booleanToBool :: (CFLP s, BooleanSolver (Ctx s))
>               => Data s Boolean -> Context (Ctx s) -> Data s Bool
> booleanToBool b = withHNF b $ \b c@(Context cs) ->
>   case b of
>     FreeVar u x -> Typed $ 
>       maybe (return (FreeVar u (untyped (ifThenElse (Typed x) true false c))))
>             (untyped . nondet)
>             (lookupBoolean (label u) cs)
>     Delayed check resume -> Typed $ do
>       narrowed <- check c
>       if narrowed
>        then untyped (booleanToBool (Typed (resume c)) c)
>        else return (Delayed check
>               (\c -> untyped (booleanToBool (Typed (resume c)) c)))
>     _ -> ifThenElse (Typed (return b)) true false c

