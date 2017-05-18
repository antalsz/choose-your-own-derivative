{-# LANGUAGE KindSignatures, TypeOperators, PolyKinds, DataKinds, GADTs,
             TypeInType, TypeFamilies, UndecidableInstances, RankNTypes,
             ScopedTypeVariables, AllowAmbiguousTypes, TypeApplications,
             LambdaCase, EmptyCase, MultiParamTypeClasses, FlexibleInstances
#-}
{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors #-}

module Equiv where

import Data.Type.Equality
import Data.Constraint
import Data.Singletons
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Prelude.Tuple
import Data.Kind (type (*))
import Data.Typeable (Proxy(..))

import Constraints
import Types
import NFI

-- Equivalence with respect to a domain
data Equiv (env1 :: TypingCtx) (env2  :: TypingCtx) (dom  :: Ctx ()) where
  Equiv :: forall (env1 :: TypingCtx) (env2 :: TypingCtx) (dom :: Ctx ()).
           Sing env1 -> Sing env2 -> Sing dom
        -> (forall x. Dict (Lookup dom x ~ Just '()) -> Sing x -> Equiv1 env1 env2 x)
        -> Equiv env1 env2 dom

-- Two environments are equivalent at a variable if they are either
-- syntactically equal (EquivEq) or semantically equal (EquivJust), meaning
-- that they map to equivalent closures
data Equiv1 (env1 :: TypingCtx) (env2 :: TypingCtx) x where
  EquivEq :: (LookupT env1 x ~ LookupT env2 x)
          => Equiv1 env1 env2 x
  EquivJust    :: ( LookupT env1 x ~ Just '(env1',s),
                    LookupT env2 x ~ Just '(env2',s) )
               => EquivFMType env1' env2' s -> Equiv1 env1 env2 x

-- Two environments are equivalent at a type s
-- if they are equivalent on the domain of s
data EquivFMType (env1 :: TypingCtx) (env2 :: TypingCtx) s where
  EquivFree :: WS dom s
            -> Equiv env1 env2 dom
            -> EquivFMType env1 env2 s


-- WS dom s says that the type s uses at most the variables in dom
data WS (dom :: Ctx ()) s where
  WSVar  :: Lookup dom x ~ Just '() => Sing x -> WS dom (Var x)
  WSZero :: WS dom Zero
  WSOne  :: WS dom One
  WSPlus :: WS dom s1 -> WS dom s2 -> WS dom (s1 :+: s2)
  WSTimes:: WS dom s1 -> WS dom s2 -> WS dom (s1 :×: s2)
  WSMu   :: Sing x -> WS (Add dom x '()) t -> WS dom (Mu x t)
  WSSubst :: WS (Add dom x '()) t -> Sing x -> WS dom s -> WS dom (Subst t x s)
  WSFunctorial :: WS dom t -> WS dom (Functorial t)
  WSPrim       :: WS dom (Prim a)

wfSFMType :: WS env s -> Sing s
wfSFMType (WSVar x)        = SVar x
wfSFMType WSZero           = SZero
wfSFMType WSOne            = SOne
wfSFMType (WSPlus s1 s2)   = SPlus (wfSFMType s1) (wfSFMType s2)
wfSFMType (WSTimes s1 s2)  = STimes (wfSFMType s1) (wfSFMType s2)
wfSFMType (WSMu x t)       = SMu x (wfSFMType t)
wfSFMType (WSSubst t x s)  = SSubst (wfSFMType t) x (wfSFMType s)
wfSFMType (WSFunctorial t) = SFunctorial (wfSFMType t)
wfSFMType WSPrim           = SPrim

------------------------------------------------------------

equivCoerce :: forall f (env1 :: TypingCtx) (env2 :: TypingCtx)
               (dom :: Ctx ()) (t :: FMType). Functor f
            => WS dom t -> Equiv env1 env2 dom
            -> Interp f env1 t -> Interp f env2 t
equivCoerce (WSVar x) (Equiv _ _ _ f) v =
  case lookupSingletonT x of { Dict ->
    case f Dict x of
      EquivEq -> v
      EquivJust (EquivFree s pf) -> equivCoerce @f s pf v
  }
equivCoerce WSZero          _  v          = v
equivCoerce (WSPlus s1 _)   eq (Left  v1) = Left  $ equivCoerce @f s1 eq v1
equivCoerce (WSPlus _ s2)   eq (Right v2) = Right $ equivCoerce @f s2 eq v2
equivCoerce WSOne           _  v          = v
equivCoerce (WSTimes s1 s2) eq (v1,v2)    =
    (equivCoerce @f s1 eq v1, equivCoerce @f s2 eq v2)
equivCoerce (WSMu x t)      eq (Con v)    =
    Con $ equivSubstCoerce @f t x (WSMu x t) eq v
equivCoerce (WSSubst t x s) eq v          = equivSubstCoerce @f t x s eq v
equivCoerce (WSFunctorial t)eq v          = equivCoerce @f t eq <$> v
equivCoerce WSPrim          _  v          = v

equivSubstCoerce :: forall f dom x s t env1 env2. Functor f
                 => WS (Add dom x '()) t -> Sing x -> WS dom s
                 -> Equiv env1 env2 dom
                 -> Interp f (AddT env1 x s) t
                 -> Interp f (AddT env2 x s) t
equivSubstCoerce t x s eq v = equivCoerce @f t eq' v
  where
    eq' :: Equiv (AddT env1 x s) (AddT env2 x s) (Add dom x '())
    eq' = equivAdd x s eq


equivEmpty :: forall env1 env2. (SingI env1, SingI env2)
           => Equiv env1 env2 Empty
equivEmpty = Equiv (sing :: Sing env1) (sing :: Sing env2) SEmpty $ \case

equivWeaken :: forall x (s :: FMType) dom (env1 :: TypingCtx) (env2 :: TypingCtx).
               Dict (Lookup dom x ~ Nothing)
            -> Sing x -> Sing s
            -> Equiv env1 env2 dom -> Equiv env1 (AddT env2 x s) dom
equivWeaken pf x s (Equiv env1 env2 dom f) = Equiv env1 env2' dom $ \Dict y ->
    ifEqNat x y
        (case pf of) -- inaccessible code
        (case lookupAddNEqT @s env2 y x of {Dict ->
         case f Dict y of
           EquivEq       -> EquivEq
           EquivJust pf' -> EquivJust pf'
        })
  where
    env2' = addT env2 x s

equivRefl :: Sing env0 -> Sing env -> Equiv env0 env0 env
equivRefl env0 env = Equiv env0 env0 env $ \Dict _ -> EquivEq




equivAdd :: forall x s env1 env2 env. Sing x -> WS env s -> Equiv env1 env2 env
         -> Equiv (AddT env1 x s) (AddT env2 x s) (Add env x '())
equivAdd x s pf@(Equiv env1 env2 dom f) = Equiv env1' env2' dom' $ \Dict y ->
    ifEqNat x y (case lookupAddEqT @s env1 x of { Dict ->
                 case lookupAddEqT @s env2 x of { Dict ->
                 EquivJust $ EquivFree s pf }})
                (case lookupAddNEq  dom y x (Proxy :: Proxy '()) of {Dict ->
                 case lookupAddNEqT @s env1 y x of {Dict ->
                 case lookupAddNEqT @s env2 y x of {Dict ->
                 case f Dict y of
                   EquivEq -> EquivEq
                   EquivJust pf' -> EquivJust pf'
                }}})
  where
    env1' = addT env1 x s'
    env2' = addT env2 x s'
    dom'  = add dom x STuple0
    s' = wfSFMType s


-- FreeIn ------------------------------

data HasDomain (t :: FMType) where
  Domain :: Sing dom -> WS dom t -> HasDomain t

hasDomain :: forall t. Sing t -> HasDomain t
hasDomain = \case
    SVar x -> case lookupSingletonEq @NCtx x (Proxy :: Proxy '()) of
                Dict -> Domain (singletonMap x STuple0) (WSVar x)
    SZero  -> Domain SEmpty WSZero
    SOne   -> Domain SEmpty WSOne
    (SPlus t1 t2) ->
      case (hasDomain t1, hasDomain t2) of {(Domain dom1 t1', Domain dom2 t2') ->
      let t1'' = wsMergeL dom1 dom2 t1'
          t2'' = wsMergeR dom1 dom2 t2'
      in Domain (dom1 ⋓ dom2) $ WSPlus t1'' t2''
      }
    (STimes t1 t2) ->
      case (hasDomain t1, hasDomain t2) of {(Domain dom1 t1', Domain dom2 t2') ->
      let t1'' = wsMergeL dom1 dom2 t1'
          t2'' = wsMergeR dom1 dom2 t2'
      in Domain (dom1 ⋓ dom2) $ WSTimes t1'' t2''
      }
    (SMu x t)      -> hasDomainMu x (hasDomain t)
    (SSubst t x s) -> hasDomainSubst (hasDomain t) x (hasDomain s)
    SFunctorial t  -> case hasDomain t of
                        Domain dom t' -> Domain dom $ WSFunctorial t'
    SPrim          -> Domain SEmpty WSPrim

hasDomainMu :: forall x t. Sing x -> HasDomain t -> HasDomain (Mu x t)
hasDomainMu x (Domain (dom :: Sing dom) t) =
    case eqRefl x of Dict -> Domain dom' (WSMu x $ wsAddRemove x x dom t)
  where
    dom' :: Sing (Remove x dom)
    dom' = remove x dom

hasDomainSubst :: forall t x s.
                  HasDomain t -> Sing x -> HasDomain s -> HasDomain (Subst t x s)
hasDomainSubst (Domain (dom1 :: Sing dom1) t) x (Domain (dom2 :: Sing dom2) s) =
    Domain (dom1' ⋓ dom2) $ WSSubst t' x (wsMergeR dom1' dom2 s)
  where
    dom1' :: Sing (Remove x dom1)
    dom1' = remove x dom1

    t' :: WS (Add (Merge (Ctx ()) (Remove x dom1) dom2) x '()) t
    t' = case addDistrL dom1' dom2 x of {Dict ->
         case eqRefl x of {Dict ->
         wsMergeL (add dom1' x STuple0) dom2 $ wsAddRemove x x dom1 t
         }}


-- TODO
-- data SubCtx k (ctx1 :: Ctx k) (ctx2 :: Ctx k) where
--   SubCtx :: (forall x v. Lookup ctx1 x ~ Just v 
--          => Dict (Lookup ctx2 x ~ Just v)) -> SubCtx k ctx1 ctx2

type SubCtx' (ctx1 :: map k) (ctx2 :: map k) =
    (forall x v. Dict (Lookup ctx1 x ~ Just v)
         -> Sing x -> Sing v -> Dict (Lookup ctx2 x ~ Just v))
data SubCtx map k :: map k -> map k -> * where
  SubCtx :: Sing ctx1 -> Sing ctx2 -> SubCtx' ctx1 ctx2 -> SubCtx map k ctx1 ctx2

getCtx1 :: SubCtx map k ctx1 ctx2 -> Sing ctx1
getCtx1 (SubCtx γ1 _ _) = γ1

getCtx2 :: SubCtx map k ctx1 ctx2 -> Sing ctx2
getCtx2 (SubCtx _ γ2 _) = γ2

getpf :: SubCtx map k ctx1 ctx2 -> SubCtx' ctx1 ctx2
getpf (SubCtx _ _ pf) = pf

subCtxWS :: forall dom1 dom2 t. SubCtx Ctx () dom1 dom2 -> WS dom1 t -> WS dom2 t
subCtxWS pf (WSVar x)               = case getpf pf Dict x STuple0 of Dict -> WSVar x
subCtxWS _  WSZero                  = WSZero
subCtxWS _  WSOne                   = WSOne
subCtxWS pf (WSPlus s1 s2)          = WSPlus (subCtxWS pf s1) (subCtxWS pf s2)
subCtxWS pf (WSTimes s1 s2)         = WSTimes (subCtxWS pf s1) (subCtxWS pf s2)
subCtxWS pf (WSMu (x :: Sing x) t)  = WSMu x (subCtxWS pf' t)
  where
    pf' :: SubCtx Ctx () (Add dom1 x '()) (Add dom2 x '())
    pf' = subAddTrans x STuple0 pf
subCtxWS pf (WSSubst t (x :: Sing x) s) = WSSubst (subCtxWS pf' t) x (subCtxWS pf s)
  where
    pf' :: SubCtx Ctx () (Add dom1 x '()) (Add dom2 x '())
    pf' = subAddTrans x STuple0 pf
subCtxWS pf (WSFunctorial t)= WSFunctorial (subCtxWS pf t)
subCtxWS _  WSPrim          = WSPrim

subMergeL :: Sing ctx1 -> Sing ctx2 -> SubCtx Ctx () ctx1 (Merge (Ctx ()) ctx1 ctx2)
subMergeL γ1@(SN _) γ2@SEmpty   = SubCtx γ1 (γ1 ⋓ γ2) (\ Dict _ _ -> Dict)
subMergeL (SN γ1) (SN γ2)       = SubCtx (SN γ1) (SN (γ1 ⋓ γ2)) (subMergeNL γ1 γ2) 
subMergeL SEmpty SEmpty         = SubCtx SEmpty SEmpty $ \case
subMergeL SEmpty (SN γ2)        = SubCtx SEmpty (SN γ2) $ \case

subMergeNL :: Sing ctx1 -> Sing ctx2 -> SubCtx' ctx1 (Merge (NCtx ()) ctx1 ctx2)
subMergeNL (SEnd STuple0) (SEnd STuple0)            Dict SZ STuple0 = Dict
subMergeNL (SEnd STuple0) (SCons SNothing _)        Dict SZ STuple0 = Dict
subMergeNL (SEnd STuple0) (SCons (SJust STuple0) _) Dict SZ STuple0 = Dict
--subMergeNL (SEnd STuple0) _                         Dict _  STuple0 = 
--    error "Inaccessible code in subMergeNL (SEnd _) _ SZ _"
subMergeNL (SCons _ _) (SEnd STuple0)               Dict SZ     STuple0 = Dict
subMergeNL (SCons _ _) (SEnd STuple0)               Dict (SS _) STuple0 = Dict
subMergeNL (SCons _ _) (SCons SNothing _)           Dict SZ     STuple0 = Dict
subMergeNL (SCons _ _) (SCons (SJust STuple0) _)    Dict SZ     STuple0 = Dict
subMergeNL (SCons _ γ1) (SCons _ γ2)                Dict (SS x) STuple0 =
    case subMergeNL γ1 γ2 Dict x STuple0 of Dict -> Dict

subMergeR :: Sing ctx1 -> Sing ctx2 -> SubCtx Ctx () ctx2 (Merge (Ctx ()) ctx1 ctx2)
subMergeR ctx1 ctx2 = case mergeSymm ctx1 ctx2 of Dict -> subMergeL ctx2 ctx1


subAddTrans :: forall k (v :: k) x (dom1 :: Ctx k) dom2 .
               Sing x -> Sing v 
            -> SubCtx Ctx k dom1 dom2 -> SubCtx Ctx k (Add dom1 x v) (Add dom2 x v)
subAddTrans x v sub = SubCtx (add dom1 x v) (add dom2 x v) 
                           $ subAddTrans' @k @v x dom1 dom2 sub
  where
    dom1 = getCtx1 sub
    dom2 = getCtx2 sub

subAddTrans' :: forall k (v :: k) x (dom1 :: Ctx k) dom2 .
               Sing x -> Sing dom1 -> Sing dom2
            -> SubCtx Ctx k dom1 dom2 -> SubCtx' (Add dom1 x v) (Add dom2 x v)
subAddTrans' x dom1 dom2 pf Dict y v' = ifEqNat x y 
    (case lookupAddEq dom1 x pv of {Dict -> 
     case lookupAddEq dom2 x pv of {Dict -> Dict}})
    (case lookupAddNEq dom1 y x pv of {Dict ->
     case lookupAddNEq dom2 y x pv of {Dict -> getpf pf Dict y v'}})
  where
    pv = (Proxy :: Proxy v)

subEmptyL :: Sing dom -> SubCtx Ctx () Empty dom
subEmptyL γ = SubCtx SEmpty γ $ \case

subWeaken :: forall x (dom :: Ctx ()).  Sing dom -> Sing x
          -> SubCtx Ctx () dom (Add dom x '())
subWeaken γ x = SubCtx γ (add γ x STuple0) $ subWeaken' γ x

subWeaken' :: forall x (dom :: Ctx ()).  Sing dom -> Sing x
          -> SubCtx' dom (Add dom x '())
subWeaken' γ x Dict y STuple0 = ifEqNat x y (lookupAddEq γ x (Proxy :: Proxy '()))
                                           (lookupAddNEq γ y x (Proxy :: Proxy '()))

subAddRemove :: Sing dom -> Sing x -> SubCtx Ctx () dom (Add (Remove x dom) x '())
subAddRemove γ x = SubCtx γ (add (remove x γ) x STuple0) $ subAddRemove' γ x

subAddRemove' :: Sing dom -> Sing x -> SubCtx' dom (Add (Remove x dom) x '())
subAddRemove' γ x Dict y STuple0 =
  ifEqNat x y (lookupAddEq γ' x p)
              (case lookupAddNEq γ' y x p of {Dict ->
               case lookupRemoveNEq y x γ of {Dict -> 
               Dict}})
    where
    p = (Proxy :: Proxy '())
    γ' = remove x γ

-- Corollaries
wsMergeL :: Sing dom1 -> Sing dom2 -> WS dom1 t -> WS (Merge (Ctx ()) dom1 dom2) t
wsMergeL dom1 dom2 = subCtxWS $ subMergeL dom1 dom2

wsMergeR :: Sing dom1 -> Sing dom2 -> WS dom2 t -> WS (Merge (Ctx ()) dom1 dom2) t
wsMergeR dom1 dom2 = subCtxWS $ subMergeR dom1 dom2

wsAdd :: forall x dom t. Sing x -> Sing dom -> WS dom t -> WS (Add dom x '()) t
wsAdd x dom ws_t = subCtxWS (subWeaken dom x) ws_t

wsAddRemove :: (x == y) ~ True
            => Sing x -> Sing y -> Sing dom -> WS dom t -> WS (Add (Remove x dom) y '()) t
wsAddRemove x y dom ws_t = 
  case eqEq x y of Dict -> subCtxWS (subAddRemove dom x) ws_t 




-- NIS -------------------------------------------------

data NotInScope x t where
  NIS :: forall (dom :: Ctx ()) x t.
         Lookup dom x ~ (Nothing :: Maybe ())
      => Sing x -> Sing dom -> WS dom t -> NotInScope x t

nfi_nis :: Sing x -> NFI.NotFreeIn x t -> NotInScope x t
nfi_nis x (NFIVar y) =
  case lookupSingletonNEq @Ctx x y (Proxy :: Proxy '()) of {Dict ->
  case lookupSingletonEq @Ctx y (Proxy :: Proxy '()) of {Dict ->
    NIS x (singletonMap y STuple0) $ WSVar y
  }}
nfi_nis x NFIZero             = NIS x SEmpty WSZero
nfi_nis x NFIOne              = NIS x SEmpty WSOne
nfi_nis x (NFIPlus t1 t2)     =
  case nfi_nis x t1 of {NIS _ dom1 t1' ->
  case nfi_nis x t2 of {NIS _ dom2 t2' ->
  case lookupMerge dom1 dom2 x of {Dict ->
      NIS x (dom1 ⋓ dom2) $ WSPlus (wsMergeL dom1 dom2 t1') (wsMergeR dom1 dom2 t2')
  }}}
nfi_nis x (NFITimes t1 t2)    =
  case nfi_nis x t1 of {NIS _ dom1 t1' ->
  case nfi_nis x t2 of {NIS _ dom2 t2' ->
  case lookupMerge dom1 dom2 x of {Dict ->
      NIS x (dom1 ⋓ dom2) $ WSTimes (wsMergeL dom1 dom2 t1') (wsMergeR dom1 dom2 t2')
  }}}
nfi_nis x (NFIMuEq y t)       = nfiMuEq x y (hasDomain t)
nfi_nis x (NFIMuNEq y t)      = nfiMuNEq y (nfi_nis x t)
nfi_nis x (NFISubstEq t y s)  = nfiSubstEq (hasDomain t) y (nfi_nis x s)
nfi_nis x (NFISubstNEq t y s) = nfiSubstNEq (nfi_nis x t) y (nfi_nis x s)
nfi_nis x (NFIFunctorial t)   = case nfi_nis x t of
    NIS _ dom t' -> NIS x dom (WSFunctorial t')
nfi_nis x NFIPrim             = NIS x SEmpty WSPrim

nfiMuEq :: forall x y t. ((x==y) ~ True) 
        => Sing x -> Sing y -> HasDomain t -> NotInScope x (Mu y t)
nfiMuEq x y (Domain (dom :: Sing dom) t) = 
    case eqEq x y of {Dict -> 
    case lookupRemove y dom of {Dict ->
      NIS x dom' (WSMu y t')
    }}
  where
    dom' :: Sing (Remove x dom)
    dom' = remove x dom

    t' :: WS (Add (Remove x dom) y '()) t
    t' = wsAddRemove x y dom t

nfiMuNEq :: forall x y t. ((x==y) ~ False) 
         => Sing y -> NotInScope x t -> NotInScope x (Mu y t)
nfiMuNEq y (NIS x (dom :: Sing dom) t) = 
    case lookupRemoveNEq x y dom of {Dict ->
      NIS x (remove y dom) $ WSMu y t'
    }
  where
    t' :: WS (Add (Remove y dom) y '()) t
    t' = case eqRefl y of Dict -> wsAddRemove y y dom t

nfiSubstEq :: forall x y s t. ((x == y) ~ True)
           => HasDomain t -> Sing y -> NotInScope x s -> NotInScope x (Subst t y s)
nfiSubstEq (Domain (dom1 :: Sing dom1) t) y (NIS x (dom2 :: Sing dom2) s) =
  case lookupMerge dom1' dom2 x of {Dict ->
  case lookupRemove x dom1 of {Dict ->
    NIS x (dom1' ⋓ dom2) $ WSSubst t' y s'
  }}
  where
    dom1' :: Sing (Remove x dom1)
    dom1' = remove x dom1

    s' :: WS (Merge (Ctx ()) (Remove x dom1) dom2) s
    s' = wsMergeR dom1' dom2 s

    t' :: WS (Add (Merge (Ctx ()) (Remove x dom1) dom2) y '()) t
    t' = case addDistrL dom1' dom2 y of {Dict ->
           wsMergeL (add dom1' y STuple0) dom2 $ wsAddRemove x y dom1 t
         }


nfiSubstNEq :: forall x y s t.
               NotInScope x t -> Sing y -> NotInScope x s -> NotInScope x (Subst t y s)
nfiSubstNEq (NIS _ (dom1 :: Sing dom1) t) y (NIS x (dom2 :: Sing dom2) s) =
  case lookupMerge dom1 dom2 x of {Dict ->
    NIS x (dom1 ⋓ dom2) (WSSubst t' y s')
  }
  where
    s' :: WS (Merge (Ctx ()) dom1 dom2) s
    s' = wsMergeR dom1 dom2 s
    t' :: WS (Add (Merge (Ctx ()) dom1 dom2) y '()) t
    t' = wsAdd y (dom1 ⋓ dom2) (wsMergeL dom1 dom2 t)




----------------------------------------
-- Weakening ---------------------------
----------------------------------------

nfiEquiv :: forall s x t env. Sing x -> NFI.NotFreeIn x t -> Sing s -> Sing env
         -> EquivFMType env (AddT env x s) t
nfiEquiv x pf s env = case nfi_nis x pf of
    (NIS _ dom t) -> EquivFree t (equivWeaken Dict x s (equivRefl env dom))

weakening :: forall f x s t env. (Functor f) =>
             Sing x -> NFI.NotFreeIn x t -> Sing s -> Sing env
          -> Interp f env t -> Interp f (AddT env x s) t
weakening x nfi s env t = case nfiEquiv x nfi s env of {EquivFree ws eq ->
                          equivCoerce @f ws eq t }
