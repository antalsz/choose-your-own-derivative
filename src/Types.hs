{-# LANGUAGE KindSignatures, TypeOperators, PolyKinds, DataKinds, GADTs,
             TypeInType, TypeFamilies, UndecidableInstances, RankNTypes,
             ScopedTypeVariables, AllowAmbiguousTypes, TypeApplications,
             LambdaCase, MultiParamTypeClasses, FlexibleInstances
#-}
{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors #-}

module Types where

import Data.Type.Equality
import Data.Constraint

import Data.Kind (type (*))
import Data.Void
import Data.Type.Bool
import Data.Singletons
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Prelude.Tuple
import Data.Typeable (Proxy(..))

import Constraints

-- FMType' is indexed by the type of variables
data FMType' id where
  Var        :: id -> FMType' id
  Zero       :: FMType' id
  One        :: FMType' id
  (:+:)      :: FMType' id -> FMType' id -> FMType' id
  (:×:)      :: FMType' id -> FMType' id -> FMType' id
  Mu         :: id -> FMType' id -> FMType' id
  Subst      :: FMType' id -> id -> FMType' id -> FMType' id -- order is (t | x = s)
  Functorial :: FMType' id -> FMType' id
  Prim       :: * -> FMType' id
infixr 6 :+:
infixr 7 :×:








type FMType = FMType' Nat

data instance Sing (t :: FMType' id) :: * where
  SVar        :: Sing x -> Sing ('Var x)
  SZero       :: Sing 'Zero
  SOne        :: Sing 'One
  SPlus       :: Sing t1 -> Sing t2 -> Sing (t1 ':+: t2)
  STimes      :: Sing t1 -> Sing t2 -> Sing (t1 ':×: t2)
  SMu         :: Sing x   -> Sing t  -> Sing (Mu x t)
  SSubst      :: Sing t  -> Sing x   -> Sing s -> Sing (Subst t x s)
  SFunctorial :: Sing t  -> Sing (Functorial t)
  SPrim       :: Sing (Prim a)

instance (SingI x)                   => SingI ('Var x)       where sing = SVar sing
instance                                SingI Zero           where sing = SZero
instance                                SingI One            where sing = SOne
instance (SingI t1, SingI t2)        => SingI (t1 :+: t2)    where sing = SPlus sing sing
instance (SingI t1, SingI t2)        => SingI (t1 :×: t2)    where sing = STimes sing sing
instance (SingI x, SingI    t)       => SingI (Mu x t)       where sing = SMu sing sing
instance (SingI t, SingI x, SingI s) => SingI (Subst t x s)  where sing = SSubst sing sing sing
instance (SingI t)                   => SingI (Functorial t) where sing = SFunctorial sing
instance                                SingI (Prim a)       where sing = SPrim

-- Fresh function ---------------------------------------------

type family FreshFor (t :: FMType) :: Nat where
  FreshFor (Var x)        = S x
  FreshFor Zero           = Z
  FreshFor One            = Z
  FreshFor (s :+: t)      = Max (FreshFor s) (FreshFor t)
  FreshFor (s :×: t)      = Max (FreshFor s) (FreshFor t)
  FreshFor (Mu x t)       = Max (S x) (FreshFor t)
  FreshFor (Subst t x s)  = S x `Max` FreshFor t `Max` FreshFor s
  FreshFor (Functorial t) = FreshFor t
  FreshFor (Prim a)       = Z

sFreshFor :: Sing t -> Sing (FreshFor t)
sFreshFor = \case
  SVar x        -> SS x
  SZero         -> SZ
  SOne          -> SZ
  SPlus t1 t2   -> sMax (sFreshFor t1) (sFreshFor t2)
  STimes t1 t2  -> sMax (sFreshFor t1) (sFreshFor t2)
  SMu x t2      -> sMax (SS x) (sFreshFor t2)
  SSubst t x s  -> SS x `sMax` sFreshFor t `sMax` sFreshFor s
  SFunctorial t -> sFreshFor t
  SPrim         -> SZ



-- typing contexts are contexts of closures
data TypingCtx = TypingCtx (Ctx (TypingCtx,FMType))
type EmptyT = 'TypingCtx 'Empty

emptyT :: Sing EmptyT
emptyT = STypingCtx SEmpty

type family LookupT (ctx :: TypingCtx) (i :: Nat) :: Maybe (TypingCtx,FMType) where
  LookupT ('TypingCtx ctx) i = Lookup ctx i
type family AddT (ctx :: TypingCtx) (x :: Nat) (t :: FMType) :: TypingCtx where
  AddT ('TypingCtx ctx) x t = 'TypingCtx (Add ctx x '( 'TypingCtx ctx, t ))
type SingletonMapT (x :: Nat) (t :: FMType) = 'TypingCtx (SingletonMap x '(EmptyT, t))


data instance Sing (g :: TypingCtx) where
  STypingCtx :: Sing g -> Sing ('TypingCtx g)

instance SingI g => SingI ('TypingCtx g) where
  sing = STypingCtx sing

type Value f t = Interp f EmptyT t
type family Interp' (f :: * -> *) (closure :: (TypingCtx,FMType)) :: * where
  Interp' f '(env,t) = Interp f env t











type family Interp (f :: * -> *) (env :: TypingCtx) (t :: FMType) :: * where
 Interp f env (Var x)         = Interp' f (FromJust (LookupT env x))
 Interp f env Zero            = Void
 Interp f env (t₁ ':+: t₂)    = Either (Interp f env t₁) (Interp f env t₂)
 Interp f env One             = ()
 Interp f env (t₁ ':×: t₂)    = (Interp f env t₁, Interp f env t₂)
 Interp f env (Mu x t)        = Fix f env t x (Mu x t)
 Interp f env (Subst t x s)   = Interp f (AddT env x s) t -- Fix f env t x s
 Interp f env (Functorial t)  = f (Interp f env t)
 Interp f env (Prim a)        = a


















newtype Fix (f :: * -> *) (env :: TypingCtx)
            (t :: FMType) (x :: Nat) (s :: FMType) :: * where
  Con :: forall (f :: * -> *) (env :: TypingCtx)
            (t :: FMType) (x :: Nat) (s :: FMType). Interp f (AddT env x s) t -> Fix f env t x s


-- Helper Functions for contexts

addT :: forall (t :: FMType) ctx x.
        Sing (ctx :: TypingCtx) -> Sing (x :: Nat) -> Sing t
     -> Sing (AddT ctx x t)
addT (STypingCtx ctx) x t = STypingCtx $ add ctx x (STuple2 (STypingCtx ctx) t)

singletonMapT :: forall (t :: FMType) x. Sing x -> Sing t -> Sing (SingletonMapT x t)
singletonMapT x t = STypingCtx $ singletonMap x (STuple2 emptyT t)

lookupAddEqT :: forall (t :: FMType) x (ctx :: TypingCtx).
                Sing ctx -> Sing x -> Dict (LookupT (AddT ctx x t) x ~ Just '(ctx,t))
lookupAddEqT (STypingCtx ctx) x = lookupAddEq ctx x (Proxy :: Proxy '(ctx,t))

lookupAddNEqT :: forall (t :: FMType) x (ctx :: TypingCtx) y.
                 (x==y)~'False
              => Sing ctx -> Sing x -> Sing y -> Dict (LookupT (AddT ctx y t) x ~ LookupT ctx x)
lookupAddNEqT (STypingCtx ctx) x y = lookupAddNEq ctx x y (Proxy :: Proxy '(ctx,t))

lookupSingletonT :: forall (t :: FMType) x.
                    Sing x -> Dict (LookupT (SingletonMapT x t) x ~ Just '(EmptyT,t))
lookupSingletonT x = lookupSingletonEq @Ctx x (Proxy :: Proxy '(EmptyT,t))

lookupSingletonNEqT :: forall (t :: FMType) x y. (x==y) ~ 'False
                    => Sing x -> Sing y -> Dict (LookupT (SingletonMapT y t) x ~ Nothing)
lookupSingletonNEqT x y = lookupSingletonNEq @Ctx x y (Proxy :: Proxy '(EmptyT,t))

--------------------------------------------------------------------------------

-- Needed for 'ToFM'

type family (x :: id) `FreeIn` (t :: FMType' id) :: Bool where
  x `FreeIn` 'Var y       = x == y
  x `FreeIn` Zero         = False
  x `FreeIn` One          = False
  x `FreeIn` (s :+: t)    = (x `FreeIn` s) || (x `FreeIn` t)
  x `FreeIn` (s :×: t)    = (x `FreeIn` s) || (x `FreeIn` t)
  x `FreeIn` Mu y t       = If (x==y) False (x `FreeIn` t)
  x `FreeIn` Subst s y t  = x `FreeIn` t || If (x==y) False (x `FreeIn` s)
  x `FreeIn` Functorial t = x `FreeIn` t
  x `FreeIn` Prim t       = False
