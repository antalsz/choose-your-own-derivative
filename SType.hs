{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, RankNTypes, ConstraintKinds, GADTs,
             DataKinds, PolyKinds, FlexibleContexts,
             TypeInType, TypeApplications, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module SType where

import Derivatives
import Constraints

import GHC.TypeLits
import Data.Proxy
import Unsafe.Coerce
import Data.Kind hiding (Type)
import Data.Reflection
import Data.Function

data SType (t :: Type) :: ★ where
  SVar        :: KnownNat x => SType ('Var x)
  SZero       :: SType 'Zero
  SOne        :: SType 'One
  SPlus       :: SType t1 -> SType t2 -> SType (t1 ':+: t2)
  STimes      :: SType t1 -> SType t2 -> SType (t1 ':×: t2)
  SMu         :: KnownNat x => SType t -> SType ('Mu x t)
  SFunctorial :: SType t -> SType ('Functorial t)

data SWrt (w :: Wrt') :: ★ where
  SWrtVar     :: KnownNat x => SWrt ('WrtVar' x)
  SWrtFunctor :: SWrt 'WrtFunctor'

class                             Infer (t :: Type)     where infer :: SType t
instance KnownNat x            => Infer ('Var x)        where infer = SVar
instance                          Infer 'Zero           where infer = SZero
instance                          Infer 'One            where infer = SOne
instance (Infer x, Infer y)    => Infer (x ':+: y)      where infer = SPlus infer infer
instance (Infer x, Infer y)    => Infer (x ':×: y)      where infer = STimes infer infer
instance (KnownNat x, Infer t) => Infer ('Mu x t)       where infer = SMu infer
instance Infer t               => Infer ('Functorial t) where infer = SFunctorial infer

type InferTo m a = Infer (ConvType m a)
type InferToV a  = InferTo 'Nothing a
type InferToF f a = InferTo ('Just f) a

-- Handy shortcuts for STypes ------------------------------------------

toSDMu' :: forall z y w t. (KnownNat z, KnownNat y) => SWrt w -> SType t -> SType (DMu' w z y t)
toSDMu' w t =
  SPlus (toSSubst @y (SMu @y t) (toSD' w t))
        (STimes (toSSubst @y (SMu @y t) (toSD' (SWrtVar @y) t)) (SVar @z))

toSD' :: forall w t. SWrt w -> SType t -> SType (D' w t)
toSD' = \case
  w@SWrtVar ->
    w & \(_ :: SWrt ('WrtVar' x)) -> \case
          v@SVar -> v & \(_ :: SType ('Var y)) -> ifEqNat @x @y SOne SZero
          mu@(SMu s) -> mu & \(_ :: SType ('Mu y s)) ->
            case freshKnown mu of
              Dict -> ifEqNat @x @y SZero (toSDMu @(FreshFor t) @y w s)
          (SPlus t1 t2)            -> SPlus (toSD' w t1) (toSD' w t2)
          (STimes t1 t2)           -> SPlus (STimes (toSD' w t1) t2)
                                            (STimes t1 (toSD' w t2))
          SZero                    -> SZero
          SOne                     -> SZero
          (SFunctorial _)          -> SZero
  w@SWrtFunctor ->
    w & \(_ :: SWrt 'WrtFunctor') -> \case
          SVar -> SZero
          mu@(SMu s) -> mu & \(_ :: SType ('Mu y s)) ->
            case freshKnown mu of
              Dict -> toSDMu @(FreshFor t) @y SWrtFunctor s
          (SPlus t1 t2)            -> SPlus (toSD' w t1) (toSD' w t2)
          (STimes t1 t2)           -> SPlus (STimes (toSD' w t1) t2)
                                            (STimes t1 (toSD' w t2))
          SZero                    -> SZero
          SOne                     -> SZero
          (SFunctorial t) -> t

toSDMu :: forall z y w t. (KnownNat z, KnownNat y)
       => SWrt w -> SType t -> SType (DMu w z y t)
toSDMu w t =
  SMu @z $ SPlus (toSSubst @y smu (toSD' w t))
                (STimes (toSSubst @y smu (toSD' (SWrtVar @y) t)) (SVar @z))
  where
    smu = SMu @y t

toSSubst :: forall x s t. KnownNat x => SType s -> SType t -> SType (Subst x s t)
toSSubst s v@SVar          =
  v & \(_ :: SType ('Var y)) -> ifEqNat @x @y s SVar
toSSubst _ SZero           = SZero
toSSubst _ SOne            = SOne
toSSubst s (SPlus t1 t2)   = SPlus (toSSubst @x s t1) (toSSubst @x s t2)
toSSubst s (STimes t1 t2)  = STimes (toSSubst @x s t1) (toSSubst @x s t2)
toSSubst s mu@(SMu u)      =
  mu & \(_ :: SType ('Mu y u)) -> ifEqNat @x @y mu (SMu (toSSubst @x s u))
toSSubst s (SFunctorial t) = SFunctorial (toSSubst @x s t)

-- Proofs using STypes ------------------------------------------------------

-- TODO: freshKnown, freshNotFree, freshFreeInSubst

freshFor :: forall t. SType t -> Integer
freshFor v@SVar          = v & \(_ :: SType ('Var x)) ->
                                 succ (natVal $ Proxy @x)
freshFor SZero           = 0
freshFor SOne            = 0
freshFor (SPlus s t)     = freshFor s `max` freshFor t
freshFor (STimes s t)    = freshFor s `max` freshFor t
freshFor mu@(SMu t)      = mu & \(_ :: SType ('Mu x s)) ->
                                  succ (natVal $ Proxy @x) `max` freshFor t
freshFor (SFunctorial t) = freshFor t

freshKnown :: SType t -> Dict (KnownNat (FreshFor t))
freshKnown t =
  reifyNat (freshFor t) $
    \(Proxy :: Proxy n) ->
      unsafeCoerce (Dict @(KnownNat n))

freshForSum :: ((FreshFor t1 `FreeIn` t1) ~ 'False, (FreshFor t2 `FreeIn` t2) ~ 'False)
            => SType t1 -> SType t2
            -> Dict ((FreshFor (t1 ':+: t2) `FreeIn` (t1 ':+: t2)) ~ 'False)
freshForSum = undefined

freshForTimes ::  ((FreshFor t1 `FreeIn` t1) ~ 'False, (FreshFor t2 `FreeIn` t2) ~ 'False)
              => SType t1 -> SType t2
              -> Dict ((FreshFor (t1 ':×: t2) `FreeIn` (t1 ':×: t2)) ~ 'False)
freshForTimes = undefined

freshNotFree :: SType t -> Dict ((FreshFor t `FreeIn` t) ~ 'False)
freshNotFree SVar           = unsafeCoerce ()
freshNotFree SZero          = Dict
freshNotFree SOne           = Dict
freshNotFree (SPlus  t1 t2) =
    case (freshNotFree t1, freshNotFree t2) of {(Dict,Dict) ->
    case freshForSum t1 t2                  of {Dict        ->
    Dict }}
freshNotFree (STimes t1 t2) =
    case (freshNotFree t1, freshNotFree t2) of {(Dict,Dict) ->
    case freshForTimes t1 t2                of {Dict        ->
    Dict }}
freshNotFree (SMu _)        = undefined
freshNotFree (SFunctorial t)=
    case freshNotFree t                     of {Dict        ->
    Dict }

freshFreeInSubst :: forall x s t. FreeIn x s ~ 'False
                 => Dict ((FreeIn (FreshFor s) (Subst x s t)) ~ 'False)
freshFreeInSubst = undefined

freshFreeInSubst' :: forall x w t. KnownNat x => SWrt w -> SType t
    -> Dict ((FreeIn (FreshFor ('Mu x t)) (Subst x ('Mu x t) (D' w t))) ~ 'False)
freshFreeInSubst' _ t =
    case freshNotFree (SMu @x t) of
      Dict -> freshFreeInSubst @x @('Mu x t) @(D' w t)
