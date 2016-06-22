{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, RankNTypes, ConstraintKinds, GADTs,
             DataKinds, PolyKinds, PartialTypeSignatures, TypeApplications, RecursiveDo, TypeInType #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Locations where

import Derivatives
import Constraints
import SType
import Value

import GHC.TypeLits

import Data.Type.Equality
import Data.Void
import Data.Function
import Data.Kind


locations :: forall f env t. Functor f
          => SType t -> Value f env t
          -> [ f (Value f env (D' 'WrtFunctor' t)) ]
locations SVar            _           = []
locations SOne            _           = []
locations SZero           _           = []
locations (SPlus t1 _)    (Inl v)     =
    (Inl <$>) <$> locations t1 v
locations (SPlus _ t2)    (Inr v)     =
    (Inr <$>) <$> locations t2 v
locations (STimes t1 t2)  (v1 :&: v2) =
    ((Inl . (:&: v2) <$>) <$> locations t1 v1) ++
    ((Inr . (v1 :&:) <$>) <$> locations t2 v2)
locations x@(SMu t)       v           =
  x & \(_ :: SType ('Mu x s)) -> locationsMu @x t v
locations (SFunctorial _) (Impure v)  = [v]

locationsMu :: forall x t env f. (KnownNat x, Functor f) =>
               SType t
            -> Value f env ('Mu x t)
            -> [ f (Value f env (DMu 'WrtFunctor' (FreshFor ('Mu x t)) x t)) ]
locationsMu t v =
    let locs1 = locations t unwrappedv
        ls1   = fromLocs1 locs1
        locs2 = locationsAt @('[] :: [(Nat, ★)]) @env @_ @x smu t unwrappedv
        ls2   = fromLocs2 locs2
    in ls1 ++ ls2
  where
    unwrappedv :: Value f (UpdateEnv x f ('Mu x t) env) t
    unwrappedv = unwrapValue @x t v

    fromLocs1 locs1 = [ fun1 <$> e | e <- locs1 ]
    fun1     :: Value f (UpdateEnv x f ('Mu x t) env) (D' 'WrtFunctor' t)
             -> Value f env (DMu 'WrtFunctor' (FreshFor ('Mu x t)) x t)
    fun1 d = injectDMu @x SWrtFunctor t (Left d)

    fromLocs2 :: [ (Value f (UpdateEnv x f ('Mu x t) env) (D' ('WrtVar' x) t),
                       Value f env ('Mu x t)) ]
              -> [ f (Value f env (DMu 'WrtFunctor' (FreshFor ('Mu x t)) x t)) ]
    fromLocs2 = concatMap fromLocsAt

    fromLocsAt :: (Value f (UpdateEnv x f ('Mu x t) env) (D' ('WrtVar' x) t),
                   Value f env ('Mu x t))
               -> [ f (Value f env (DMu 'WrtFunctor' (FreshFor ('Mu x t)) x t)) ]
    fromLocsAt (d, v') = fun <$> locationsMu @x t v'
      where
        fun :: f (Value f env (DMu 'WrtFunctor' (FreshFor ('Mu x t)) x t))
            -> f (Value f env (DMu 'WrtFunctor' (FreshFor ('Mu x t)) x t))
        fun = fmap (\d' -> injectDMu @x SWrtFunctor t (Right(d,d')))

    smu      :: SType ('Mu x t)
    smu      = SMu @x t


locationsAt :: forall env env' env0 x s t f.
               (KnownNat x,
                Value f env0 s ~ Lookup (Append env ('(x,Value f env0 s) ': env')) Void x,
                Functor f)
            => SType s -> SType t
            -> Value f (Append env ('(x,Value f env0 s) ': env')) t
            -> [ (Value f (Append env ('(x,Value f env0 s) ': env'))
                          (D' ('WrtVar' x) t),
                  Value f env0 s) ]
locationsAt _ (SFunctorial _) _             = []
locationsAt _ y@SVar          (Val v)       =
  y & \(_ :: SType ('Var y)) ->
    ifEqNat @x @y
    [ (The,v) ]
    []
locationsAt _ SOne            _             = []
locationsAt _ SZero           _             = []
locationsAt s (SPlus t1 _ )   (Inl v)       =
    let locs = locationsAt @env @env' @env0 @x s t1 v
    in [ fun e | e <- locs ]
  where
    fun (d,v') = (Inl d, v')
locationsAt s (SPlus _ t2)    (Inr v)       =
    let locs = locationsAt @env @env' @env0 @x s t2 v
    in [ fun e | e <- locs ]
  where
    fun (d,v') = (Inr d, v')
locationsAt s (STimes t1 t2)  (v1 :&: v2)   =
    let locsLeft  = locationsAt @env @env' @env0 @x s t1 v1
        locsRight = locationsAt @env @env' @env0 @x s t2 v2
    in [ funLeft e | e <- locsLeft ] ++ [ funRight e | e <- locsRight]
  where
    funLeft  (d,v) = (Inl (d :&: v2), v)
    funRight (d,v) = (Inr (v1 :&: d), v)
locationsAt s y@(SMu t)       v             =
  y & \(_ :: SType ('Mu y u)) ->
    ifEqNat @x @y []
      (locationsAtMu @env @env' @env0 @x @y s t v)




locationsAtMu :: forall env env' env0 x y s t f.
               (KnownNat x, KnownNat y,
                (x == y) ~ 'False, (y == x) ~ 'False,
                Value f env0 s ~ Lookup (Append env ('(x,Value f env0 s) ': env')) Void x,
                Functor f)
            => SType s -> SType t
            -> Value f (Append env ('(x,Value f env0 s) ': env')) ('Mu y t)
            -> [ (Value f (Append env ('(x,Value f env0 s) ': env'))
                          (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
                  Value f env0 s) ]
locationsAtMu s t v =
  case lookupConsNeq @x @(Value f (Append env ('(x,Value f env0 s) ': env')) ('Mu y t))
                     @y @(Append env ('(x,Value f env0 s) ': env')) @Void of
    Dict ->
      let locs1 =
            locationsAt @('(y, Value f (Append env ('(x,Value f env0 s) ': env')) ('Mu y t)) ': env) @env' @env0 @x s t unwrappedv
          ls1   = fromLocs1 locs1
          locs2 =
            locationsAt @'[] @((Append env ('(x,Value f env0 s) ': env'))) @(Append env ('(x,Value f env0 s) ': env')) @y smu t unwrappedv
          ls2   = fromLocs2 locs2
      in ls1 ++ ls2
  where

    unwrappedv :: Value f (UpdateEnv y f ('Mu y t) (Append env ('(x,Value f env0 s) ': env'))) t
    unwrappedv =  unwrapValue @y t v

    fromLocs1 :: [ (Value f (UpdateEnv y f ('Mu y t) (Append env ('(x,Value f env0 s) ': env'))) (D' ('WrtVar' x) t),
                    Value f env0 s) ]
              -> [ (Value f (Append env ('(x,Value f env0 s) ': env'))
                            (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
                    Value f env0 s) ]
    fromLocs1 locs1 = [ fun1 e | e <- locs1 ]

    fun1 :: (Value f (UpdateEnv y f ('Mu y t) (Append env ('(x,Value f env0 s) ': env'))) (D' ('WrtVar' x) t),
             Value f env0 s)
         -> (Value f (Append env ('(x,Value f env0 s) ': env')) (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
             Value f env0 s)
    fun1 (d,v') = (injectDMu @y wrtx t (Left d), v')

    fromLocs2 :: [ (Value f (UpdateEnv y f ('Mu y t) (Append env ('(x,Value f env0 s) ': env'))) (D' ('WrtVar' y) t),
                       Value f (Append env ('(x,Value f env0 s) ': env')) ('Mu y t)) ]
              -> [ (Value f (Append env ('(x,Value f env0 s) ': env')) (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
                          Value f env0 s) ]
    fromLocs2 = concatMap fromLocsAt

    fromLocsAt :: (Value f (UpdateEnv y f ('Mu y t) (Append env ('(x,Value f env0 s) ': env'))) (D' ('WrtVar' y) t),
                   Value f (Append env ('(x,Value f env0 s) ': env')) ('Mu y t))
               -> [ (Value f (Append env ('(x,Value f env0 s) ': env')) (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
                           Value f env0 s) ]
    fromLocsAt (d,v') =
        let ls  = locationsAtMu @env @env' @env0 @x @y s t v'
        in concatMap fromLocsAt' ls
      where
        fromLocsAt' ::  (Value f (Append env ('(x,Value f env0 s) ': env')) (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
                         Value f env0 s)
                    ->  [ (Value f (Append env ('(x,Value f env0 s) ': env')) 
                                     (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t),
                                 Value f env0 s) ]
        fromLocsAt' (d',v'') = [ (injectDMu @y wrtx t $ Right (d,d'), v'') ]

    wrtx     :: SWrt ('WrtVar' x)
    wrtx     = SWrtVar @x
    smu      :: SType ('Mu y t)
    smu      =  SMu @y t
