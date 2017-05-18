{-# LANGUAGE KindSignatures, TypeOperators, PolyKinds, DataKinds, GADTs,
             TypeInType, TypeFamilies, UndecidableInstances, RankNTypes,
             ScopedTypeVariables, AllowAmbiguousTypes, TypeApplications,
             LambdaCase
#-}
{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
--{-# OPTIONS_GHC -fno-warn-unused-variables #-}
-- WARNING "Turn off -fno-warn-unused-variables"

module NFI  where
import Data.Type.Equality
import Data.Constraint

import Constraints
import Types
import Derivatives


data NotFreeIn (x :: Nat) (t :: FMType) where
  NFIVar        :: ((x == y) ~ False, (y==x) ~ False)
                => Sing y -> NotFreeIn x (Var y)
  NFIZero       :: NotFreeIn x Zero
  NFIOne        :: NotFreeIn x One
  NFIPlus       :: NotFreeIn x t -> NotFreeIn x s -> NotFreeIn x (t :+: s)
  NFITimes      :: NotFreeIn x t -> NotFreeIn x s -> NotFreeIn x (t :×: s)
  NFIMuEq       :: ((x == y) ~ True)  => Sing y -> Sing t -> NotFreeIn x (Mu y t)
  NFIMuNEq      :: ((x == y) ~ False) => Sing y -> NotFreeIn x t -> NotFreeIn x (Mu y t)
  NFISubstEq    :: ((x == y) ~ True)  => Sing t -> Sing y -> NotFreeIn x s -> NotFreeIn x (Subst t y s)
  NFISubstNEq   :: ((x == y) ~ False) => NotFreeIn x t -> Sing y
                -> NotFreeIn x s -> NotFreeIn x (Subst t y s)
  NFIFunctorial :: NotFreeIn x t -> NotFreeIn x (Functorial t)
  NFIPrim       :: NotFreeIn x (Prim a)

infixr 6 `NFIPlus`
infixr 7 `NFITimes`

nfiToSing :: x `NotFreeIn` t -> Sing t
nfiToSing (NFIVar y)          = SVar y
nfiToSing NFIZero             = SZero
nfiToSing NFIOne              = SOne
nfiToSing (l `NFIPlus`  r)    = nfiToSing l `SPlus`  nfiToSing r
nfiToSing (l `NFITimes` r)    = nfiToSing l `STimes` nfiToSing r
nfiToSing (NFIMuEq  y t)      = SMu y t
nfiToSing (NFIMuNEq y t)      = SMu y $ nfiToSing t
nfiToSing (NFISubstEq  t y s) = SSubst t y (nfiToSing s)
nfiToSing (NFISubstNEq t y s) = SSubst (nfiToSing t) y (nfiToSing s)
nfiToSing (NFIFunctorial t)   = SFunctorial $ nfiToSing t
nfiToSing NFIPrim             = SPrim

-- Claim 1: (FreshFor t) is not free in t

nfiFreshFor :: Sing t -> FreshFor t `NotFreeIn` t
nfiFreshFor t = case geRefl t_fresh of Dict -> geFreshForNFI t_fresh t
  where
    t_fresh = sFreshFor t

geFreshForNFI :: (x >= FreshFor t) ~ True => Sing x -> Sing t -> x `NotFreeIn` t
geFreshForNFI x = \case
  SVar y        -> case succGeTrue x y of Dict -> NFIVar y
  SZero         -> NFIZero
  SOne          -> NFIOne
  SPlus t1 t2   -> case maxGeTrans x (sFreshFor t1) (sFreshFor t2) of
                     Dict -> NFIPlus (geFreshForNFI x t1) (geFreshForNFI x t2)
  STimes t1 t2  -> case maxGeTrans x (sFreshFor t1) (sFreshFor t2) of
                     Dict -> NFITimes (geFreshForNFI x t1) (geFreshForNFI x t2)
  SMu y t       -> nfiMu x y t
  SSubst t y s  -> nfiSubst x t y s
  SFunctorial t -> NFIFunctorial $ geFreshForNFI x t
  SPrim         -> NFIPrim



nfiMu :: x >= Max (S y) (FreshFor t) ~ True
       => Sing x -> Sing y -> Sing t -> x `NotFreeIn` 'Mu y t
nfiMu x y t = case maxGeTrans x (SS y) (sFreshFor t) of {Dict ->
              case succGeTrue x y of {Dict ->
                NFIMuNEq y $ geFreshForNFI x t
              }}

nfiSubst :: (x >= (S y `Max` FreshFor t `Max` FreshFor s)) ~ True
         => Sing x -> Sing t -> Sing y -> Sing s
         -> x `NotFreeIn` 'Subst t y s
nfiSubst x t y s = case maxGeTrans x (sMax (SS y) fresh_t) fresh_s of {Dict ->
                   case maxGeTrans x (SS y) fresh_t of {Dict ->
                   case succGeTrue x y of {Dict ->
                   NFISubstNEq (geFreshForNFI x t) y (geFreshForNFI x s)
                   }}}
  where
    fresh_t = sFreshFor t
    fresh_s = sFreshFor s

-- Claim 2: derivatives

-- type DMu (w :: Wrt) (z :: Nat) (y :: Nat) (t :: FMType) =
--   'Mu z (DSubst w t y ('Mu y t) ('Var z))

nfiD :: forall (w :: Wrt) (x :: Nat) (t :: FMType).
        Sing w -> Sing x -> x `NotFreeIn` t -> x `NotFreeIn` D' w t

nfiD (SWrtVar y) _ (NFIVar z) = ifEqNat y z NFIOne NFIZero
nfiD SWrtFunctor _ (NFIVar _) = NFIZero

nfiD _ _ NFIZero = NFIZero
nfiD _ _ NFIOne  = NFIZero

nfiD w x (nfiL `NFIPlus`  nfiR)            = nfiD w x nfiL `NFIPlus` nfiD w x nfiR
nfiD w x (nfiL `NFITimes` nfiR)            = (nfiD w x nfiL `NFITimes` nfiR) `NFIPlus`
                                             (nfiL `NFITimes` nfiD w x nfiR)

nfiD (SWrtVar y) x (NFIMuEq z t) =
  ifEqNat y z
    NFIZero
    (ifEqNat x fresh
      (NFIMuEq  fresh (sDSubst (SWrtVar y) t z (SMu z t) (SVar x)))
      (NFIMuNEq fresh (NFISubstEq (sD (SWrtVar y) t) z (NFIMuEq z t) `NFIPlus`
                       NFISubstEq (sD (SWrtVar z) t) z (NFIMuEq z t) `NFITimes`
                       NFIVar fresh)))
  where fresh = sMax (SS z) (sFreshFor t)
nfiD (SWrtVar y) x (NFIMuNEq z t) =
  ifEqNat y z
    NFIZero
    (ifEqNat x fresh
      (NFIMuEq  fresh (sDSubst (SWrtVar y) st z (SMu z st) (SVar x)))
      (NFIMuNEq fresh ((NFISubstNEq (nfiD (SWrtVar y) x t) z (NFIMuNEq z t)) `NFIPlus`
                       (NFISubstNEq (nfiD (SWrtVar z) x t) z (NFIMuNEq z t) `NFITimes`
                        NFIVar fresh))))
  where st    = nfiToSing t
        fresh = sMax (SS z) (sFreshFor st)

nfiD SWrtFunctor x (NFIMuEq y t) =
    ifEqNat x fresh
      (NFIMuEq  fresh (sDSubst SWrtFunctor t y (SMu y t) (SVar x)))
      (NFIMuNEq fresh (NFISubstEq (sD SWrtFunctor t) y (NFIMuEq y t) `NFIPlus`
                       NFISubstEq (sD (SWrtVar y) t) y (NFIMuEq y t) `NFITimes`
                       NFIVar fresh))
  where fresh = sMax (SS y) (sFreshFor t)
nfiD SWrtFunctor x (NFIMuNEq y t) =
  ifEqNat x fresh
    (NFIMuEq  fresh (sDSubst SWrtFunctor st y (SMu y st) (SVar x)))
    (NFIMuNEq fresh ((NFISubstNEq (nfiD SWrtFunctor x t) y (NFIMuNEq y t)) `NFIPlus`
                     (NFISubstNEq (nfiD (SWrtVar y) x t) y (NFIMuNEq y t) `NFITimes`
                      NFIVar fresh)))
  where st    = nfiToSing t
        fresh = sMax (SS y) (sFreshFor st)


nfiD (SWrtVar y) x (NFISubstEq t z nfiResult)             =
  ifEqNat y z
    (NFISubstEq (sD (SWrtVar y) t) z nfiResult `NFITimes`
     nfiD (SWrtVar y) x nfiResult)
    ((NFISubstEq (sD (SWrtVar y) t) z nfiResult) `NFIPlus`
     (NFISubstEq (sD (SWrtVar z) t) z nfiResult `NFITimes`
      nfiD (SWrtVar y) x nfiResult))
nfiD (SWrtVar y) x (NFISubstNEq nfiBody z nfiResult) =
  ifEqNat y z
    (NFISubstNEq (nfiD (SWrtVar y) x nfiBody) z nfiResult `NFITimes`
     nfiD (SWrtVar y) x nfiResult)
    ((NFISubstNEq (nfiD (SWrtVar y) x nfiBody) z nfiResult) `NFIPlus`
     (NFISubstNEq (nfiD (SWrtVar z) x nfiBody) z nfiResult `NFITimes`
      nfiD (SWrtVar y) x nfiResult))

nfiD SWrtFunctor x (NFISubstEq t y nfiResult) =
  (NFISubstEq (sD SWrtFunctor t) y nfiResult) `NFIPlus`
  (NFISubstEq (sD (SWrtVar y) t) y nfiResult `NFITimes` nfiD SWrtFunctor x nfiResult)
nfiD SWrtFunctor x (NFISubstNEq nfiBody y nfiResult) =
  (NFISubstNEq (nfiD SWrtFunctor x nfiBody) y nfiResult) `NFIPlus`
  (NFISubstNEq (nfiD (SWrtVar y) x nfiBody) y nfiResult `NFITimes`
   nfiD SWrtFunctor x nfiResult)

nfiD (SWrtVar _) _ (NFIFunctorial _)   = NFIZero
nfiD SWrtFunctor _ (NFIFunctorial nfi) = nfi

nfiD _ _ NFIPrim                           = NFIZero
