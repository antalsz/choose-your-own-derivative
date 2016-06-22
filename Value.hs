{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, RankNTypes, ConstraintKinds, GADTs,
             DataKinds, PolyKinds, ViewPatterns, TypeApplications #-}
{-# OPTIONS_GHC -Wall -fno-warn-redundant-constraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Value where

import Derivatives
import Constraints
import SType

import GHC.TypeLits
import Data.Void
import Data.Monoid
import Data.Type.Equality
import Data.Function

import Unsafe.Coerce

-- Value env t : values v such that env |- v : t
data Value (f :: ★ -> ★) (env :: [(id, ★)]) :: Type' id -> ★ where
  Val    :: Lookup env Void x -> Value f env ('Var x)

  The    :: Value f env 'One

  Inl    :: Value f env t1 -> Value f env (t1 ':+: t2)
  Inr    :: Value f env t2 -> Value f env (t1 ':+: t2)

  (:&:)  :: Value f env t1 -> Value f env t2 -> Value f env (t1 ':×: t2)

  Wrap   :: Value f env (Subst x ('Mu x t) t) -> Value f env ('Mu x t)

  Impure :: f (Value f env t) -> Value f env ('Functorial t)

infixr 9 :&:

unwrap :: Value f env ('Mu x t) -> Value f env (Subst x ('Mu x t) t)
unwrap (Wrap v) = v

type UpdateEnv x f s env = '(x,Value f env s) ': env

-- Equality instances for the Value f env t types --------------------------------

instance Eq (Lookup env Void x) => Eq (Value f env ('Var x)) where
  Val a1 == Val a2 = a1 == a2

instance Eq (Value f env 'Zero) where
  v1 == v2 = case v1 of {} `seq` case v2 of {}

instance Eq (Value f env 'One) where
  The == The = True

instance (Eq (Value f env t1), Eq (Value f env t2)) => Eq (Value f env (t1 ':+: t2)) where
  Inl v1 == Inl v2 = v1 == v2
  Inr v1 == Inr v2 = v1 == v2
  Inl _  == Inr _  = False
  Inr _  == Inl _  = False

instance (Eq (Value f env t1), Eq (Value f env t2)) => Eq (Value f env (t1 ':×: t2)) where
  (v11 :&: v12) == (v21 :&: v22) = v11 == v21 && v12 == v22

instance Eq (Value f env (Subst x ('Mu x t) t)) => Eq (Value f env ('Mu x t)) where
  Wrap v1 == Wrap v2 = v1 == v2

instance Eq (f (Value f env t)) => Eq (Value f env ('Functorial t)) where
  Impure v1 == Impure v2 = v1 == v2


-- Ord instances for the Value f env t types -------------------------------------


instance Ord (Lookup env Void x) => Ord (Value f env ('Var x)) where
  a1 `compare` a2 = a1 `compare` a2

instance Ord (Value f env 'Zero) where
  v1 `compare` v2 = case v1 of {} `seq` case v2 of {}

instance Ord (Value f env 'One) where
  The `compare` The = EQ

instance (Ord (Value f env t1), Ord (Value f env t2)) => Ord (Value f env (t1 ':+: t2)) where
  Inl v1 `compare` Inl v2 = v1 `compare` v2
  Inr v1 `compare` Inr v2 = v1 `compare` v2
  Inl _  `compare` Inr _  = LT
  Inr _  `compare` Inl _  = GT

instance (Ord (Value f env t1), Ord (Value f env t2)) => Ord (Value f env (t1 ':×: t2)) where
  (v11 :&: v12) `compare` (v21 :&: v22) = (v11 `compare` v21) <> (v12 `compare` v22)

instance Ord (Value f env (Subst x ('Mu x t) t)) => Ord (Value f env ('Mu x t)) where
  Wrap v1 `compare` Wrap v2 = v1 `compare` v2

instance Ord (f (Value f env t)) => Ord (Value f env ('Functorial t)) where
  Impure v1 `compare` Impure v2 = v1 `compare` v2


-- Show instances for the Value f env t types ------------------------------------


show_app :: Show a => Int -> String -> a -> ShowS
show_app p con val = showParen (p > app_prec) $
                       showString (con ++ " ") . showsPrec (app_prec+1) val
  where app_prec = 10 :: Int
{-# INLINABLE show_app #-}

instance Show (Lookup env Void x) => Show (Value f env ('Var x)) where
  showsPrec p (Val a) = show_app p "Val" a

instance Show (Value f env 'Zero) where
  showsPrec _ = \case

instance Show (Value f env 'One) where
  showsPrec _ The = showString "The"

instance (Show (Value f env t1), Show (Value f env t2)) => Show (Value f env (t1 ':+: t2)) where
  showsPrec p (Inl v1) = show_app p "Inl" v1
  showsPrec p (Inr v2) = show_app p "Inr" v2

instance (Show (Value f env t1), Show (Value f env t2)) => Show (Value f env (t1 ':×: t2)) where
  showsPrec p (v1 :&: v2) = showParen (p > op_prec) $
                              showsPrec (op_prec+1) v1 .
                              showString " :&: " .
                              showsPrec (op_prec+1) v2
    where op_prec = 9 :: Int

instance Show (Value f env (Subst x ('Mu x t) t)) => Show (Value f env ('Mu x t)) where
  showsPrec p (Wrap v) = show_app p "Wrap" v

instance Show (f (Value f env t)) => Show (Value f env ('Functorial t)) where
  showsPrec p (Impure v) = show_app p "Impure" v


-- Substitution via the environment to Value --------------------------------

explicitSubst :: forall x s t env f. (Functor f, KnownNat x, (x `FreeIn` s) ~ 'False)
              => SType s -> SType t
              -> Value f env (Subst x s t)
              -> Value f ('(x,Value f env s)': env) t
explicitSubst _ y@SVar v = y & \(_ :: SType ('Var y)) ->
    ifEqNat @x @y
    (Val v)
    (weakening @x y v)
explicitSubst _ y@SZero        v           = weakening @x y v
explicitSubst _ y@SOne         v           = weakening @x y v
explicitSubst s (SPlus  t1 _ ) (Inl v1)    = Inl (explicitSubst @x s t1 v1)
explicitSubst s (SPlus  _  t2) (Inr v2)    = Inr (explicitSubst @x s t2 v2)
explicitSubst s (STimes t1 t2) (v1 :&: v2) =
              (explicitSubst @x s t1 v1 :&: explicitSubst @x s t2 v2)
explicitSubst s mu@(SMu u) v = mu & \(_ :: SType ('Mu y u)) ->
    ifEqNat @x @y
    (weakening @x mu v)
    (Wrap $ explicitSubst @x s (toSSubst @y mu u)
          $ substReassoc @x @y @s @('Mu y u) u
          $ unwrap v)
explicitSubst s (SFunctorial t) (Impure v) =
    Impure $ fmap (explicitSubst @x s t) v


explicitUnsubst :: forall x s t f env. (Functor f, KnownNat x, (x `FreeIn` s) ~ 'False)
              => SType s -> SType t
              -> Value f ('(x,Value f env s)': env) t
              -> Value f env (Subst x s t)
explicitUnsubst _ y@SVar (Val v) = y & \(_ :: SType ('Var y)) ->
    ifEqNat @x @y
    v
    (Val $ lookupTail @x @y @env @(Value f env s) @Void v)
explicitUnsubst _ SOne           The         = The
explicitUnsubst _ SZero          v           = case v of
explicitUnsubst s (SPlus  t1 _ ) (Inl v1)    = Inl (explicitUnsubst @x s t1 v1)
explicitUnsubst s (SPlus  _ t2 ) (Inr v2)    = Inr (explicitUnsubst @x s t2 v2)
explicitUnsubst s (STimes t1 t2) (v1 :&: v2) =
                (explicitUnsubst @x s t1 v1 :&: explicitUnsubst @x s t2 v2)
explicitUnsubst s (SFunctorial t) (Impure v) =
    Impure $ fmap (explicitUnsubst @x s t) v
explicitUnsubst s mu@(SMu u)      v          = mu & \(_ :: SType ('Mu y u)) ->
    ifEqNat @x @y (explicitUnsubstMuEq @x @y u v) (explicitUnsubstMuNeq @x @y u v)
  where
    explicitUnsubstMuEq :: forall x y u.
                           (x ~ y , KnownNat x, KnownNat y,
                            (x `FreeIn` s) ~ 'False)
                        => SType u
                        -> Value f ('(x,Value f env s) ': env) ('Mu y u)
                        -> Value f env ('Mu y u)
    explicitUnsubstMuEq u v =
      case d of
        Dict -> Wrap $ explicitUnsubst @x s ss $ unwrap v
      where
        ss :: SType (Subst y ('Mu y u) u)
        ss = toSSubst @y (SMu @y u) u

        d :: Dict (Subst x s (Subst y ('Mu y u) u) ~ Subst y ('Mu y u) u)
        d = case comprehendNFI $ notFreeUnderSubstEq @y @('Mu y u) u NFI_Mu_Eq of
              Dict -> weakeningDict @x @s ss

    explicitUnsubstMuNeq :: forall x y u. (x == y) ~ 'False
                         => SType u
                         -> Value f ('(x,Value f env s)': env) ('Mu y u)
                         -> Value f env ('Mu y (Subst x s u))
    explicitUnsubstMuNeq u v = undefined -- try to only use awesomeSubstProperty
       -- (Wrap $ substAssoc px py s smu u
       --       $ explicitUnsubst px s (toSSubst py smu u)
       --       $ unwrap v)

-- Fold & Unfold Values

unwrapValue :: forall x t f env. (KnownNat x, Functor f) => SType t
            -> Value f env ('Mu x t)
            -> Value f (UpdateEnv x f ('Mu x t) env) t
unwrapValue t (Wrap v) = explicitSubst @x (SMu @x t) t v

wrapValue :: forall x t f env. (KnownNat x, Functor f) => SType t
          -> Value f (UpdateEnv x f ('Mu x t) env) t
          -> Value f env ('Mu x t)
wrapValue t v = Wrap $ explicitUnsubst @x (SMu @x t) t v


-- Weakening and Strengthening ---------------------------------------------------

data NotFreeIn (x :: id) (t :: Type' id) where
  NFI_Var    :: (x == y) ~ 'False => x `NotFreeIn` 'Var y
  NFI_Zero   :: x `NotFreeIn` 'Zero
  NFI_One    :: x `NotFreeIn` 'One
  NFI_Plus   :: (x `NotFreeIn` s) -> (x `NotFreeIn` t)
             -> (x `NotFreeIn` (s ':+: t))
  NFI_Times  :: (x `NotFreeIn` s) -> (x `NotFreeIn` t)
             -> (x `NotFreeIn` (s ':×: t))
  NFI_Mu_Eq  :: x `NotFreeIn` 'Mu x t
  NFI_Mu_Neq :: (x == y) ~ 'False => (x `NotFreeIn` t) -> (x `NotFreeIn` 'Mu y t)
  NFI_Func   :: (x `NotFreeIn` t) -> (x `NotFreeIn` 'Functorial t)

comprehendNFI :: forall (x :: Nat) t. x `NotFreeIn` t -> Dict (x `FreeIn` t ~ 'False)
comprehendNFI = \case
  NFI_Var         -> Dict
  NFI_Zero        -> Dict
  NFI_One         -> Dict
  NFI_Plus w1 w2  ->
    case (comprehendNFI w1, comprehendNFI w2) of (Dict, Dict) -> Dict
  NFI_Times w1 w2 ->
    case (comprehendNFI w1, comprehendNFI w2) of (Dict, Dict) -> Dict
  NFI_Mu_Eq       -> Dict
  NFI_Mu_Neq w    -> case comprehendNFI w of Dict -> Dict
  NFI_Func w      -> case comprehendNFI w of Dict -> Dict

witnessNFI :: forall x t. KnownNat x => SType t -> Either (Dict (x `FreeIn` t ~ 'True)) (x `NotFreeIn` t)
witnessNFI = \case
  v@SVar -> v & \(_ :: SType ('Var y)) ->
    ifEqNat @x @y (Left Dict) (Right NFI_Var)
  SZero -> Right NFI_Zero
  SOne -> Right NFI_One
  SPlus a b ->
    case (witnessNFI @x a, witnessNFI @x b) of
      (Right w1,  Right w2)  -> Right $ NFI_Plus w1 w2
      (Right (comprehendNFI -> Dict), Left Dict) -> Left Dict
      (Left Dict, Right _) -> Left Dict
      (Left Dict, Left Dict) -> Left Dict
  STimes a b ->
    case (witnessNFI @x a, witnessNFI @x b) of
      (Right w1,  Right w2)  -> Right $ NFI_Times w1 w2
      (Right (comprehendNFI -> Dict), Left Dict) -> Left Dict
      (Left Dict, Right _) -> Left Dict
      (Left Dict, Left Dict) -> Left Dict
  mu@(SMu t) -> mu & \(_ :: SType ('Mu y s)) ->
    ifEqNat @x @y
      (Right NFI_Mu_Eq)
      (case witnessNFI @x t of
         Right w -> Right $ NFI_Mu_Neq w
         Left Dict -> Left Dict)
  SFunctorial a ->
    case witnessNFI @x a of
      Right w -> Right $ NFI_Func w
      Left Dict -> Left Dict

knownNFI :: forall x t. (KnownNat x, x `FreeIn` t ~ 'False) => SType t -> x `NotFreeIn` t
knownNFI t =
  either (\case) id $ witnessNFI @x t

weakening :: forall (x :: Nat) s t f env. (Functor f, KnownNat x, (FreeIn x t) ~ 'False)
          => SType t -> Value f env t
          -> Value f ('(x,Value f env s) ': env) t
weakening t v =
  weakening' t (knownNFI @x t) v
  where
    weakening' :: SType u -> x `NotFreeIn` u -> Value f env u
               -> Value f ('(x,Value f env s) ': env) u
    weakening' SVar            NFI_Var           = \case (Val a)    -> Val a
    weakening' (SFunctorial u) (NFI_Func w)      = \case (Impure a) -> Impure (weakening' u w <$> a)
    weakening' SOne            NFI_One           = \case The        -> The
    weakening' SZero           NFI_Zero          = \case
    weakening' (SPlus ua ub)   (NFI_Plus wa wb)  = \case
      Inl va -> Inl (weakening' ua wa va)
      Inr vb -> Inr (weakening' ub wb vb)
    weakening' (STimes ua ub)  (NFI_Times wa wb) = \case
      (va :&: vb) -> (weakening' ua wa va :&: weakening' ub wb vb)
    weakening' mu@(SMu _)      NFI_Mu_Eq         = weakenMuEq mu
    weakening' mu@(SMu _)      (NFI_Mu_Neq w)    = weakenMuNeq mu w

    weakenMuEq :: forall u. SType ('Mu x u)
               -> Value f env ('Mu x u)
               -> Value f ('(x,Value f env s) ': env) ('Mu x u)
    weakenMuEq mu@(SMu u) (Wrap b) =
      Wrap (weakening' (toSSubst @x mu u) (notFreeUnderSubstEq @x @('Mu x u) u NFI_Mu_Eq) b)

    weakenMuNeq :: forall u y. (x == y) ~ 'False => SType ('Mu y u)
                -> x `NotFreeIn` u
                -> Value f env ('Mu y u)
                -> Value f ('(x,Value f env s) ': env) ('Mu y u)
    weakenMuNeq mu@(SMu u) x_nfi_u (Wrap b) =
      Wrap (weakening' (toSSubst @y mu u) (notFreeUnderSubstNeq @x @y @('Mu y u) u (NFI_Mu_Neq x_nfi_u) x_nfi_u) b)

weakeningDict :: forall (x :: Nat) s t. (KnownNat x, (FreeIn x t) ~ 'False)
              => SType t -> Dict (Subst x s t ~ t)
weakeningDict t =
  weakeningDict' t (knownNFI @x t)
  where
    weakeningDict' :: SType u -> x `NotFreeIn` u -> Dict (Subst x s u ~ u)
    weakeningDict' SVar            NFI_Var           = Dict
    weakeningDict' (SFunctorial u) (NFI_Func w)      =
      case weakeningDict' u w of
        Dict -> Dict
    weakeningDict' SOne            NFI_One           = Dict
    weakeningDict' SZero           NFI_Zero          = Dict
    weakeningDict' (SPlus ua ub)   (NFI_Plus wa wb)  =
      case (weakeningDict' ua wa, weakeningDict' ub wb) of
        (Dict, Dict) -> Dict
    weakeningDict' (STimes ua ub)  (NFI_Times wa wb) =
      case (weakeningDict' ua wa, weakeningDict' ub wb) of
        (Dict, Dict) -> Dict
    weakeningDict' mu@(SMu _)      NFI_Mu_Eq         = weakenMuEq mu
    weakeningDict' mu@(SMu _)      (NFI_Mu_Neq w)    = weakenMuNeq mu w

    weakenMuEq :: SType ('Mu x u) -> Dict (Subst x s ('Mu x u) ~ ('Mu x u))
    weakenMuEq (SMu _) = Dict

    weakenMuNeq :: (x == y) ~ 'False
                => SType ('Mu y u) -> x `NotFreeIn` u
                -> Dict (Subst x s ('Mu y u) ~ ('Mu y u))
    weakenMuNeq (SMu u) x_nfi_u =
      case weakeningDict' u x_nfi_u of
        Dict -> Dict

notFreeUnderSubstNeq :: forall x y s t.
                     (KnownNat x, KnownNat y, (x == y) ~ 'False)
                     => SType t
                     -> x `NotFreeIn` s -> x `NotFreeIn` t
                     -> x `NotFreeIn` (Subst y s t)
notFreeUnderSubstNeq t x_nfi_s x_nfi_t = undefined

-- TODO: Use this to prove SType.freshFreeInSubst?
notFreeUnderSubstEq :: forall x s t. KnownNat x
                  => SType t
                  -> x `NotFreeIn` s -> x `NotFreeIn` (Subst x s t)
notFreeUnderSubstEq t x_nfi_s =
  case t of
    v@SVar -> v & \(_ :: SType ('Var y)) ->
                    ifEqNat @x @y x_nfi_s NFI_Var
    SZero -> NFI_Zero
    SOne -> NFI_One
    SPlus t1 t2 ->
       NFI_Plus (notFreeUnderSubstEq @x t1 x_nfi_s)
                (notFreeUnderSubstEq @x t2 x_nfi_s)
    STimes t1 t2 ->
       NFI_Times (notFreeUnderSubstEq @x t1 x_nfi_s)
                 (notFreeUnderSubstEq @x t2 x_nfi_s)
    SFunctorial t' -> NFI_Func (notFreeUnderSubstEq @x t' x_nfi_s)
    mu@(SMu t') -> mu & \(_ :: SType ('Mu y t')) ->
      ifEqNat @x @y
        NFI_Mu_Eq
        (NFI_Mu_Neq (notFreeUnderSubstEq @x t' x_nfi_s))

substOverMu :: forall f (x :: Nat) s t env. Value f env ('Mu x t) -> Value f env (Subst x s ('Mu x t))
substOverMu v = v

-- what if you used explicit subsitution? then you turn Value env (Mu x t) into Value env (Subst x s (Mu x t)) --which is identical-- and then converted it into Value ((x,s):env) (Mu x t)

strengthening :: forall x v t f env. (FreeIn x t) ~ 'False
              => Value f ('(x,v) ': env) t
              -> Value f env t
strengthening v = unsafeCoerce v

-- TODO
substReassoc :: forall x y s u t f env.
                (x `FreeIn` s) ~ 'False
             => SType t
             -> Value f env (Subst y (Subst x s u) (Subst x s t))
             -> Value f env (Subst x s (Subst y u t))
substReassoc _ v = unsafeCoerce v

substAssoc :: forall f env x y s u t.
              (x `FreeIn` s) ~ 'False
           => SType t
           -> Value f env (Subst x s (Subst y u t))
           -> Value f env (Subst y (Subst x s u) (Subst x s t))
substAssoc _ v = unsafeCoerce v

awesomeSubstProperty :: forall (x :: Nat) (y :: Nat) (s :: Type' Nat) (u :: Type' Nat) (t :: Type' Nat). ((x == y) ~ 'False, (y == x) ~ 'False, y `FreeIn` s ~ 'False, KnownNat x, KnownNat y)
                     => SType t
                     -> Dict (Subst x s (Subst y u t) ~
                              Subst y (Subst x s u) (Subst x s t))
awesomeSubstProperty = \case
  z@SVar -> z & \(_ :: SType ('Var z)) ->
                  ifEqNat @z @y
                  Dict
                  (ifEqNat @z @x
                    undefined
                    undefined)
  -- TODO: FINISH THIS

-- Encoding DMu values from their components ------------------------------------

injectDMu :: forall x w t f env.
          (Functor f, KnownNat x)
          => SWrt w -> SType t
          -> Either ( Value f (UpdateEnv x f ('Mu x t) env) (D' w t) )
                    ( Value f (UpdateEnv x f ('Mu x t) env) (D' ('WrtVar' x) t),
                      Value f env (DMu w (FreshFor ('Mu x t)) x t))
          ->  Value f env (DMu w (FreshFor ('Mu x t)) x t)
injectDMu w t (Left v) = v3
  where
    v0 :: Value f env (Subst x ('Mu x t) (D' w t))
    v0 =  explicitUnsubst @x smu sdt v
    v1 :: Value f (UpdateEnv (FreshFor ('Mu x t)) f (DMu w (FreshFor ('Mu x t)) x t) env)
                  (Subst x ('Mu x t) (D' w t))
    v1 =  case (freshFreeInSubst' @x w t, freshKnown smu) of
               (Dict,Dict) -> weakening @(FreshFor ('Mu x t)) (toSSubst @x smu sdt) v0
    v2 :: Value f (UpdateEnv (FreshFor ('Mu x t)) f (DMu w (FreshFor ('Mu x t)) x t) env)
                  (DMu' w (FreshFor ('Mu x t)) x t)
    v2 =  Inl v1
    v3 :: Value f env (DMu w (FreshFor ('Mu x t)) x t)
    v3 =  case freshKnown smu of Dict -> wrapValue @(FreshFor ('Mu x t)) sdmu' v2

    sdt   :: SType (D' w t)
    sdt   =  toSD' w t
    smu   :: SType ('Mu x t)
    smu   =  SMu @x t
    sdmu' :: SType (DMu' w (FreshFor ('Mu x t)) x t)
    sdmu' =  case freshKnown smu of Dict -> toSDMu' @(FreshFor ('Mu x t)) @x w t
injectDMu w t (Right(v,v')) = v3
  where
    v0    :: Value f env (Subst x ('Mu x t) (D' ('WrtVar' x) t))
    v0    =  explicitUnsubst @x smu sdt v
    v1    :: Value f (UpdateEnv (FreshFor ('Mu x t)) f (DMu w (FreshFor ('Mu x t)) x t) env)
                     (Subst x ('Mu x t) (D' ('WrtVar' x) t))
    v1    =  case (freshFreeInSubst' @x wx t, freshKnown smu) of
                  (Dict,Dict) -> weakening @(FreshFor ('Mu x t)) (toSSubst @x smu sdt) v0
    v0'   :: Value f (UpdateEnv (FreshFor ('Mu x t)) f (DMu w (FreshFor ('Mu x t)) x t) env)
                     ('Var (FreshFor ('Mu x t)))
    v0'   =  Val v'
    v2    :: Value f (UpdateEnv (FreshFor ('Mu x t)) f (DMu w (FreshFor ('Mu x t)) x t) env)
                     (DMu' w (FreshFor ('Mu x t)) x t)
    v2    =  Inr (v1 :&: v0')
    v3    :: Value f env (DMu w (FreshFor ('Mu x t)) x t)
    v3    = case freshKnown smu of Dict -> wrapValue @(FreshFor ('Mu x t)) sdmu' v2

    wx    :: SWrt ('WrtVar' x)
    wx    =  SWrtVar @x
    sdt   :: SType (D' ('WrtVar' x) t)
    sdt   =  toSD' wx t
    smu   :: SType ('Mu x t)
    smu   =  SMu @x t
    sdmu' :: SType (DMu' w (FreshFor ('Mu x t)) x t)
    sdmu' =  case freshKnown smu of Dict -> toSDMu' @(FreshFor ('Mu x t)) @x w t

projectDMu :: forall x w t f env.
          (Functor f, KnownNat x)
          => SWrt w -> SType t
          -> Value f env (DMu w (FreshFor ('Mu x t)) x t)          
          -> Either ( Value f (UpdateEnv x f ('Mu x t) env) (D' w t) )
                    ( Value f (UpdateEnv x f ('Mu x t) env) (D' ('WrtVar' x) t),
                      Value f env (DMu w (FreshFor ('Mu x t)) x t))
projectDMu = undefined
