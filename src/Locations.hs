{-# LANGUAGE KindSignatures, TypeOperators, PolyKinds, DataKinds, GADTs,
             TypeInType, TypeFamilies, UndecidableInstances, RankNTypes,
             AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables,
             TupleSections, EmptyCase, BangPatterns
#-}
{-# OPTIONS_GHC -Wall  -fno-warn-unticked-promoted-constructors #-}


module Locations where

import Data.Type.Equality
import Data.Constraint

import Constraints
import Types
import Derivatives
import NFI
import Equiv


-- locations' t v:
-- produces a list of all of the "holes" for the functor f
locations' :: forall f t. Functor f
           => Sing t -> Value f t -> [ f (Value f (D' 'WrtFunctor t)) ]
locations' t = locations t (STypingCtx SEmpty)


locations :: forall (t :: FMType) (env :: TypingCtx) f. Functor f
          => Sing t -> Sing env
          -> Interp f env t
          -> [ f (Interp f env (D' 'WrtFunctor t)) ]
locations (SFunctorial _) _ e = [e]
locations SPrim           _ _ = []
locations (SVar _)        _ _ = []
locations SOne            _ _ = []
locations SZero           _ _ = []
locations (SPlus t1 _)    env (Left v) =
  (Left <$>) <$> locations t1 env v
locations (SPlus _ t2)    env (Right v)     =
  (Right <$>) <$> locations t2 env v
locations (STimes t1 t2)  env (v1, v2) =
    ((Left  . (,v2) <$>) <$> locations t1 env v1) ++
    ((Right . (v1,) <$>) <$> locations t2 env v2)
locations (SMu x t)      env (Con v) = locationsMu x t env v
locations (SSubst t x s) env v = locationsSubst t x s env v


locationsSubst :: forall (env :: TypingCtx) f y s t. (Functor f)
               => Sing t -> Sing y -> Sing s -> Sing env
               -> Interp f (AddT env y s) t
               -> [ f (Interp f env ('Subst (D' 'WrtFunctor t) y s
                                     ':+: ('Subst (D' ('WrtVar y) t) y s ':×: D' 'WrtFunctor s))) ]
locationsSubst t y s env v = locs1 ++ locs2
  where
    locs1 = do
        dt <- locations t (addT env y s) v
        return $ Left <$> dt

    locs2 = case lookupAddEqT @s env y of {Dict -> do
        (dyt,vs) <- locationsAt @f @s y t (addT env y s) env v
        ds       <- locations s env vs
        return $ fun2 dyt <$> ds
      }

    fun2 :: Interp f env ('Subst (D' ('WrtVar y) t) y s)
         -> Interp f env (D' 'WrtFunctor s)
         -> Interp f env (D' 'WrtFunctor ('Subst t y s))
    fun2 v1 v2 = Right(v1,v2)

locationsMu :: forall env f y t z. (Functor f, z ~ FreshFor ('Mu y t))
            => Sing y -> Sing t -> Sing env
            -> Interp f (AddT env y ('Mu y t)) t
            -> [ f (Interp f env
                   ('Mu z ('Subst (D' 'WrtFunctor t) y ('Mu y t)
                           ':+: ('Subst (D' ('WrtVar y) t) y ('Mu y t) ':×: 'Var z)))) ]
locationsMu y t env v = locs1 ++ locs2
  where
    locs1 = do
      dt <- locations t (addT env y (SMu y t)) v
      return $ fun1 <$> dt

    fun1 :: Interp f (AddT env y ('Mu y t)) (D' 'WrtFunctor t)
         -> Interp f env (D' 'WrtFunctor ('Mu y t))
    fun1 v0 =
      let v' = (weakenz pfNFI1 v0 :: Interp f (AddT env z (D' 'WrtFunctor ('Mu y t)))
                                              ('Subst (D' 'WrtFunctor t) y ('Mu y t)))
      in Con (Left v')

    dmu :: Sing (D' WrtFunctor (Mu y t))
    dmu = sD (SWrtFunctor) (SMu y t)


    weakenz :: z `NotFreeIn` t' -> Interp f env t'
            -> Interp f (AddT env z (D' 'WrtFunctor ('Mu y t))) t'
    weakenz pf v' = weakening @f z pf dmu env v'

    locs2 = case lookupAddEqT @(Mu y t) env y of {Dict -> do
        (dyt,vyt) <- locationsAt @f @('Mu y t) y t (addT env y (SMu y t)) env v
        vz        <- locations (SMu y t) env vyt
        return $ fun2 dyt <$> vz
      }

    fun2 :: Interp f env ('Subst (D' ('WrtVar y) t) y ('Mu y t))
         -> Interp f env (D' 'WrtFunctor ('Mu y t))
         -> Interp f env (D' 'WrtFunctor ('Mu y t))
    fun2 v1 v2 = case lookupAddEqT @(D' 'WrtFunctor ('Mu y t)) env z of {Dict ->
        let v1' = weakenz pfNFI2 v1
        in Con $ Right (v1',v2)
      }

    nfiMu :: z `NotFreeIn` Mu y t
    nfiMu = nfiFreshFor (SMu y t)

    -- z ~ FreshFor ('Mu y t)
    pfNFI1 :: z `NotFreeIn` 'Subst (D' 'WrtFunctor t) y ('Mu y t)
    pfNFI1 = case z_neq_y of Dict -> NFISubstNEq (nfiD SWrtFunctor z pfNFI_t) y nfiMu

    pfNFI_t :: z `NotFreeIn` t
    pfNFI_t = case freshMuNeqBoundVar y t of {Dict ->
              case nfiMu of NFIMuNEq _ pf -> pf }
    

    -- z ~ FreshFor ('Mu y t)
    pfNFI2 :: z `NotFreeIn` 'Subst (D' ('WrtVar y) t) y ('Mu y t)
    pfNFI2 = case z_neq_y of Dict -> NFISubstNEq (nfiD (SWrtVar y) z pfNFI_t) y nfiMu

    z :: Sing (FreshFor ('Mu y t))
    z = sFreshFor (SMu y t)

    z_neq_y :: Dict ((z == y) ~ False)
    z_neq_y = case geRefl z of {Dict ->
              case maxGeTrans z (SS y) (sFreshFor t) of {Dict ->
              case succGeTrue z y of {Dict ->
              Dict
              }}}


freshMuNeqBoundVar :: Sing y -> Sing t -> Dict ((FreshFor (Mu y t) == y) ~ False)
freshMuNeqBoundVar y t = 
              -- z = Max (S y) (FreshFor t)
              -- so z >= S y /\ z >= FreshFor t
              case geRefl z of {Dict ->
              case maxGeTrans z (SS y) (sFreshFor t) of {Dict ->
              -- so z != y
              case geEqFalse z y of Dict -> Dict}}
  where
    z = sFreshFor (SMu y t)

locationsAt :: forall f s env env' x t.
               (Functor f, LookupT env x ~ 'Just '(env',s))
            => Sing x -> Sing t -> Sing env -> Sing env'
            -> Interp f env t
            -> [ (Interp f env (D' ('WrtVar x) t), Interp f env' s) ]
locationsAt _ (SFunctorial _) _  _ _ = []
locationsAt x (SVar y)        _ _ v = ifEqNat x y [ ((),v) ] []
locationsAt _ SOne            _ _ _ = []
locationsAt _ SZero           _ _ _ = []
locationsAt _ SPrim           _ _ _ = []
locationsAt x (SPlus t1 _) env env' (Left  v) =
    [ fun e | e <- locationsAt @f x t1 env env' v ]
  where
    fun (d,v') = (Left d,v')
locationsAt x (SPlus _ t2) env env' (Right v) =
    [ fun e | e <- locationsAt @f x t2 env env' v ]
  where
    fun (d,v') = (Right d,v')
locationsAt x (STimes t1 t2) env env' (v1,v2) =
       [ funL e | e <- locationsAt @f x t1 env env' v1 ]
    ++ [ funR e | e <- locationsAt @f x t2 env env' v2 ]
  where
    funL (d,v) = (Left  (d,v2), v)
    funR (d,v) = (Right (v1,d), v)
locationsAt x (SMu y t)      env env' (Con v) =
    ifEqNat x y [] (locationsAtMu x y t env env' v)
locationsAt x (SSubst t y r) env env' v =
    ifEqNat x y (locationsAtSubstEq @f x t r env env' v)
                (locationsAtSubst   @f x t y r env env' v)


locationsAtMu :: forall f env env' x s y t z.
       (Functor f,
        LookupT env x ~ 'Just '(env',s), (x==y)~'False, z ~ FreshFor ('Mu y t))
    => Sing x -> Sing y -> Sing t -> Sing env -> Sing env'
    -> Interp f (AddT env y ('Mu y t)) t
    -> [ ( Interp f env ('Mu z ('Subst (D' ('WrtVar x) t) y ('Mu y t)
                               ':+: ('Subst (D' ('WrtVar y) t) y ('Mu y t)
                                    ':×: 'Var z)))
         , Interp f env' s) ]
locationsAtMu x y t env env' v = locs1 ++ locs2
  where
    locs1 = case lookupAddNEqT @('Mu y t) env x y of {Dict -> do
        ( dxt, vs ) <- locationsAt @f @s x t (addT env y (SMu y t)) env' v
        let dxt'    = weakening @f z pfNFI1 dmu env dxt
        return (Con $ Left dxt',vs)
      }

    dmu :: Sing (D' (WrtVar x) (Mu y t))
    dmu = sD (SWrtVar x) (SMu y t)


    locs2 = case lookupAddEqT @(Mu y t) env y of {Dict ->
            case lookupAddEqT @(D' (WrtVar x) (Mu y t)) env z of {Dict -> do
        (dyt,vyt)<- locationsAt @f @('Mu y t) y t (addT env y (SMu y t)) env v
        let dyt'  = weakening @f z pfNFI2 dmu env dyt
                        :: Interp f (AddT env z (D' ('WrtVar x) ('Mu y t)))
                                    ('Subst (D' ('WrtVar y) t) y ('Mu y t))
        (dxyt,vs)<- locationsAt @f @s x (SMu y t) env env' vyt
        return (Con $ Right (dyt',dxyt),vs)
      }}

    nfiMu :: z `NotFreeIn` Mu y t
    nfiMu = nfiFreshFor (SMu y t)


    pfNFI_t :: z `NotFreeIn` t
    pfNFI_t = case freshMuNeqBoundVar y t of {Dict ->
              case nfiMu of NFIMuNEq _ pf -> pf }

    -- z ~ FreshFor ('Mu y t)
    pfNFI1 :: z `NotFreeIn` 'Subst (D' ('WrtVar x) t) y ('Mu y t)
    pfNFI1 = case z_neq_y of Dict -> NFISubstNEq (nfiD (SWrtVar x) z pfNFI_t) y nfiMu

    -- z ~ FreshFor ('Mu y t)
    pfNFI2 :: z `NotFreeIn` 'Subst (D' ('WrtVar y) t) y ('Mu y t)
    pfNFI2 = case z_neq_y of Dict -> NFISubstNEq (nfiD (SWrtVar y) z pfNFI_t) y nfiMu

    z :: Sing z
    z = sFreshFor (SMu y t)

    z_neq_y :: Dict ((z == y) ~ False)
    z_neq_y = case geRefl z of {Dict ->
              case maxGeTrans z (SS y) (sFreshFor t) of {Dict ->
              case succGeTrue z y of {Dict ->
              Dict
              }}}


locationsAtSubstEq :: forall f env env' x s t r.
                      (Functor f, LookupT env x ~ 'Just '(env',s))
    => Sing x -> Sing t -> Sing r -> Sing env -> Sing env'
    -> Interp f (AddT env x r) t
    -> [ ( Interp f env ('Subst (D' ('WrtVar x) t) x r ':×: D' ('WrtVar x) r)
         , Interp f env' s) ]
locationsAtSubstEq x t r env env' v = do
    (vdt,vr) <- locsv
    (vdr,vs) <- locationsAt @f x r env env' vr
    return ((vdt, vdr), vs)
  where
    locsv :: [ (Interp f (AddT env x r) (D' ('WrtVar x) t), Interp f env r) ]
    locsv = case lookupAddEqT @r env x of
              Dict -> locationsAt @f @r x t (addT env x r) env v

locationsAtSubst :: forall f s env env' x t y r.
                    (Functor f,
                     LookupT env x ~ 'Just '(env',s), (x==y)~'False)
   => Sing x -> Sing t -> Sing y -> Sing r
   -> Sing env -> Sing env'
   -> Interp f (AddT env y r) t
   -> [ ( Interp f env ('Subst (D' ('WrtVar x) t) y r
          ':+: ('Subst (D' ('WrtVar y) t) y r ':×: D' ('WrtVar x) r))
        , Interp f env' s ) ]
locationsAtSubst x t y r env env' v = locsL ++ locsR
  where
    locsL :: [ ( Interp f env ('Subst (D' ('WrtVar x) t) y r
                  ':+: ('Subst (D' ('WrtVar y) t) y r ':×: D' ('WrtVar x) r))
               , Interp f env' s ) ]
    locsL = case lookupAddNEqT @r env x y of {Dict -> do
        (vxt,vs) <- locationsAt @f @s x t (addT env y r) env' v
        return (Left vxt, vs)
      }

    locsR :: [ ( Interp f env ('Subst (D' ('WrtVar x) t) y r
                  ':+: ('Subst (D' ('WrtVar y) t) y r ':×: D' ('WrtVar x) r))
               , Interp f env' s ) ]
    locsR = case lookupAddEqT @r env y of {Dict -> do
        (vyt,vr) <- locationsAt @f @r y t (addT env y r) env v
        (vxr,vs) <- locationsAt @f @s x r env env' vr
        return (Right (vyt,vxr), vs)
      }
