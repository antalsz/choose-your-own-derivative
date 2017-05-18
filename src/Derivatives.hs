{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, GADTs,
             DataKinds, PolyKinds, MultiParamTypeClasses,
             TypeInType, AllowAmbiguousTypes, TypeApplications #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Derivatives where

import Data.Type.Equality
import Data.Singletons.Prelude.Bool

import Constraints
import Types

data Wrt = WrtVar Nat | WrtFunctor

type family D' (w :: Wrt) (t :: FMType) :: FMType where
  D' ('WrtVar x) ('Var y)   = If (x==y) 'One 'Zero
  D' 'WrtFunctor ('Var y)   = 'Zero
  D' w           'Zero      = 'Zero
  D' w           'One       = 'Zero
  D' w           (s ':+: t) = D' w s ':+: D' w t
  D' w           (s ':×: t) = (D' w s ':×: t) ':+: (s ':×: D' w t)
  D' ('WrtVar x) ('Mu y t)  = If (x==y) 'Zero
                                 (DMu ('WrtVar x) (FreshFor ('Mu y t)) y t)
  D' 'WrtFunctor ('Mu y t)  = DMu 'WrtFunctor (FreshFor ('Mu y t)) y t
  D' ('WrtVar x) ('Subst t y s) =
     If (x==y) ('Subst (D' ('WrtVar x) t) x s ':×: D' ('WrtVar x) s)
               (DSubst ('WrtVar x) t y s (D' ('WrtVar x) s))
  D' 'WrtFunctor ('Subst t y s) =
    DSubst 'WrtFunctor t y s (D' 'WrtFunctor s)
  D' ('WrtVar x) ('Functorial t) = 'Zero
  D' 'WrtFunctor ('Functorial t) = t
  D' w           ('Prim _)       = 'Zero

type DSubst (w :: Wrt) (t :: FMType) (y :: Nat) (s :: FMType) (z :: FMType) =
  'Subst (D' w t) y s ':+: ('Subst (D' ('WrtVar y) t) y s ':×: z)
type DMu (w :: Wrt) (z :: Nat) (y :: Nat) (t :: FMType) =
  'Mu z (DSubst w t y ('Mu y t) ('Var z))

-- STypes for derivatives ---------------------------------------

data instance Sing (w :: Wrt) where
  SWrtVar :: Sing x -> Sing ('WrtVar x)
  SWrtFunctor :: Sing 'WrtFunctor

sD :: Sing w -> Sing t -> Sing (D' w t)
sD (SWrtVar x) (SVar y)         = ifEqNat x y SOne SZero
sD SWrtFunctor (SVar _)         = SZero
sD _           SZero            = SZero
sD _           SOne             = SZero
sD w           (SPlus t1 t2)    = sD w t1 `SPlus` sD w t2
sD w           (STimes t1 t2)   = (sD w t1 `STimes` t2) `SPlus` (t1 `STimes` sD w t2)
sD (SWrtVar x) (SMu y t)        = ifEqNat x y SZero (sDMu (SWrtVar x) z y t) where
    z = sFreshFor (SMu y t)
sD SWrtFunctor (SMu y t)        = sDMu SWrtFunctor z y t where
    z = sFreshFor (SMu y t)
sD (SWrtVar x) (SSubst t y s)   = ifEqNat x y eq neq where
    eq = SSubst (sD (SWrtVar x) t) x s `STimes` sD (SWrtVar y) s

    neq = sDSubst (SWrtVar x) t y s (sD (SWrtVar x) s)
sD SWrtFunctor (SSubst t  y s)  = sDSubst SWrtFunctor t y s (sD SWrtFunctor s)
sD (SWrtVar _) (SFunctorial _)  = SZero
sD SWrtFunctor (SFunctorial t)  = t
sD _           SPrim            = SZero

sDSubst :: Sing w -> Sing t -> Sing y -> Sing s -> Sing z -> Sing (DSubst w t y s z)
sDSubst w t y s z =
  SSubst (sD w t) y s `SPlus` (SSubst (sD (SWrtVar y) t) y s `STimes` z)

sDMu :: Sing w -> Sing z -> Sing y -> Sing t -> Sing (DMu w z y t)
sDMu w z y t = SMu z (sDSubst w t y (SMu y t) (SVar z))

