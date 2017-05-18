{-# LANGUAGE KindSignatures, TypeOperators, PolyKinds, DataKinds, TypeInType,
             TypeFamilies, UndecidableInstances, FlexibleContexts,
             ScopedTypeVariables, AllowAmbiguousTypes, TypeApplications,
             MultiParamTypeClasses, FlexibleInstances, EmptyCase #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module ToFM where

import Data.Kind (type (*))
import Data.Void
import Data.Singletons
import Unsafe.Coerce
import Data.Constraint
import Data.Typeable (Proxy(..))

import Constraints
import Types
import Derivatives
import Equiv


-- ToFM should always produced a closed FMType
type family ToFM (f :: Maybe (* -> *)) (α :: *) :: FMType
type instance ToFM f (α,β) = ToFM f α :×: ToFM f β
type instance ToFM f (Either α β) = ToFM f α :+: ToFM f β
type instance ToFM f [α] = FMList Z (ToFM f α)
--type instance ToFM f [α]  = Mu Z (One :+: (ToFM f α :×: Var Z))
type instance ToFM f ()   = One
type instance ToFM f Void = Zero
type instance ToFM f Char = Prim Char

--type instance ToFM (Just f) (f α) = Functorial (ToFM (Just f) α)
type instance ToFM (Just IO) (IO α) = Functorial (ToFM (Just IO) α)


class SingI (ToFM (Just f) α) => KnownFM f α where
  toFM :: α -> Value f (ToFM (Just f) α)
  fromFM :: Value f (ToFM (Just f) α) -> α
  emptyDom :: WS Empty (ToFM (Just f) α)

class KnownFM' f env α where
  toFM' :: α -> Interp f env (ToFM (Just f) α)
  fromFM' :: Interp f env (ToFM (Just f) α) -> α

instance (SingI env, KnownFM f α, Functor f) => KnownFM' f env α where
  toFM'   = equivCoerce @f (emptyDom @f @α) (equivEmpty @EmptyT @env) . toFM @f @α
  fromFM' = fromFM @f @α . equivCoerce @f (emptyDom @f @α) (equivEmpty @env @EmptyT)

-- must give functorial instances separately?
-- maybe play with defunctionalization?
instance KnownFM IO α => KnownFM IO (IO α) where
  toFM   = fmap $ toFM @IO
  fromFM = fmap $ fromFM @IO
  emptyDom = WSFunctorial $ emptyDom @IO @α
instance KnownFM IO Char where
  toFM   = id
  fromFM = id
  emptyDom = WSPrim
instance (KnownFM f α, KnownFM f β) => KnownFM f (α,β) where
  toFM (a,b) = (toFM @f a, toFM @f b)
  fromFM (a,b) = (fromFM @f a, fromFM @f b)
  emptyDom = WSTimes (emptyDom @f @α) (emptyDom @f @β)
instance (KnownFM f α, KnownFM f β) => KnownFM f (Either α β) where
  toFM (Left a)  = Left  $ toFM @f a
  toFM (Right b) = Right $ toFM @f b
  fromFM (Left a)  = Left  $ fromFM @f a
  fromFM (Right b) = Right $ fromFM @f b
  emptyDom = WSPlus (emptyDom @f @α) (emptyDom @f @β)
instance (KnownFM f α, Functor f) => KnownFM f [α] where
  toFM [] = Con (Left ())
  toFM (a:ls) = Con $ Right (a', toFM' ls)
    where a' = toFM' @f @(AddT EmptyT Z (ToFM (Just f) [α])) a
  fromFM (Con (Left ()))     = []
  fromFM (Con (Right(a,ls))) = a' : fromFM @f ls
    where a' = fromFM' @f @(AddT EmptyT Z (ToFM (Just f) [α])) a
  emptyDom = WSMu SZ $ WSPlus WSOne $ WSTimes (wsAdd SZ SEmpty $ emptyDom @f @α) 
                                              (WSVar SZ)
instance KnownFM f () where
  toFM   = id
  fromFM = id
  emptyDom = WSOne
instance KnownFM f Void where
  toFM   = id
  fromFM = id
  emptyDom = WSZero



-- Derivatives

--------------------------------------------------------------------------------
-- User-facing interface to derivatives

-- |Applies one recursive round of basic simplification steps:
--   * Adding zero.
--   * Multiplying by zero or one.
-- It might be possible to include some simple substitution resolution, too.
type family Simplify1 (t :: FMType' id) :: FMType' id where
  Simplify1 ('Zero ':+: t) = Simplify1 t
  Simplify1 (t ':+: 'Zero) = Simplify1 t
  
  Simplify1 ('One ':×: t) = Simplify1 t
  Simplify1 ('Zero ':×: t) = 'Zero
  Simplify1 (t ':×: 'One) = Simplify1 t
  Simplify1 (t ':×: 'Zero) = 'Zero

  Simplify1 (a ':+: b)      = Simplify1 a ':+: Simplify1 b
  Simplify1 (a ':×: b)      = Simplify1 a ':×: Simplify1 b
  Simplify1 ('Mu x t)       = 'Mu x (Simplify1 t)
  Simplify1 ('Subst s x t)  = 'Subst (Simplify1 s) x (Simplify1 t)
  Simplify1 ('Functorial t) = 'Functorial (Simplify1 t)
  
  Simplify1 t = t

-- |Take the fixpoint of 'Simplify1'.  If the fixpoint has converged (@t ~ t'@),
-- returns @t@; otherwise, calls 'Simplify'.
type family FixSimplify (t :: FMType' id) (t' :: FMType' id) :: FMType' id where
  FixSimplify t t  = t
  FixSimplify t t' = Simplify t'

-- |Simplify @t@ by applying basic arithmetic simplification ('Simplify1') as
-- much as possible.
type Simplify t = FixSimplify t (Simplify1 t)
--type Simplify t = Simplify1 t


data WRT a = WRTVar Nat | WRTFunctor a

-- D x a : Converts a Haskell type a into a type-level Type
type family D (x :: WRT (* -> *)) (a :: *) :: FMType where
  D ('WRTVar     x) a = D' ('WrtVar x) (ToFM 'Nothing  a)
  D ('WRTFunctor f) a = D' 'WrtFunctor (ToFM ('Just f) a)

-- DWrt x a : Converts a Haskell type a into a type-level Type
type family DWrt (x :: k) (a :: *) :: FMType where
  DWrt (x :: Nat)    a = D ('WRTVar x)     a
  DWrt (f :: * -> *) a = D ('WRTFunctor f) a

-----------------------------------
-- Type classes

class KnownSimplify1 f env t where
  simpl1 :: Interp f env t -> Interp f env (Simplify1 t)

instance KnownSimplify1 f env t => KnownSimplify1 f env (Zero :+: t) where
  simpl1 (Left x) = case x of
  simpl1 (Right v) = simpl1 @f @env @t v
instance KnownSimplify1 f env t => KnownSimplify1 f env (t :+: Zero) where
  simpl1 (Left v) = simpl1 @f @env @t v
  simpl1 (Right x) = case x of
instance KnownSimplify1 f env t => KnownSimplify1 f env (One :×: t) where
  simpl1 ((),v) = simpl1 @f @env @t v
--instance KnownSimplify1 f env t => KnownSimplify1 f env (t :×: One) where
--  simpl1 (v,()) = simpl1 @f @env @t v
instance KnownSimplify1 f env (Zero :×: t) where
  simpl1 (x,_) = x

----------------------------

wsD :: forall w env t. SingI env => Sing w -> WS env t -> WS env (D' w t)
wsD SWrtFunctor (WSVar _) = WSZero
wsD (SWrtVar y) (WSVar x) = ifEqNat x y WSOne WSZero
wsD _ WSZero = WSZero
wsD _ WSOne = WSZero
wsD w (WSPlus s1 s2) = WSPlus (wsD w s1) (wsD w s2)
wsD w (WSTimes s1 s2) = WSPlus (WSTimes (wsD w s1) s2) (WSTimes s1 (wsD w s2))
wsD SWrtFunctor (WSMu y t) = wsDMu SWrtFunctor (sFreshFor (SMu y t')) y t
    where t' = wfSFMType t
wsD (SWrtVar x) (WSMu y t) = ifEqNat x y WSZero
                           $ wsDMu (SWrtVar x) (sFreshFor (SMu y t')) y t
    where t' = wfSFMType t  
wsD SWrtFunctor (WSSubst t y s) = wsDSubst SWrtFunctor t y s (wsD SWrtFunctor s)
wsD (SWrtVar x) (WSSubst t y s) = withSingI (add (sing :: Sing env) y 
                                                 (sing :: Sing '())) $
                                  ifEqNat x y 
                                  (WSTimes (WSSubst (wsD (SWrtVar x) t) x s)
                                           (wsD (SWrtVar x) s))
                                  (wsDSubst (SWrtVar x) t y s (wsD (SWrtVar x) s))
wsD SWrtFunctor (WSFunctorial t) = t
wsD (SWrtVar _) (WSFunctorial _) = WSZero
wsD _ WSPrim = WSZero

wsDSubst :: forall env w y t s z. SingI env 
         => Sing w -> WS (Add env y '()) t -> Sing y -> WS env s -> WS env z 
         -> WS env (DSubst w t y s z)
wsDSubst w t y s z = withSingI (add (sing :: Sing env) y 
                                                 (sing :: Sing '())) $
                    WSPlus (WSSubst (wsD w t) y s)
                    (WSTimes (WSSubst (wsD (SWrtVar y) t) y s) z)

wsDMu :: forall env w z y t. SingI env 
      => Sing w -> Sing z -> Sing y -> WS (Add env y '()) t 
      -> WS env (DMu w z y t)
wsDMu w z y t = case lookupAddEq (sing :: Sing env) z (Proxy :: Proxy '()) of
                  Dict -> withSingI (add (sing :: Sing env) z (sing :: Sing '())) $
                          WSMu z $ wsDSubst w t' y (WSMu y t') (WSVar z)
  where
    t' :: WS (Add (Add env z '()) y '()) t
    t' = subCtxWS pf t
    pf :: SubCtx Ctx () (Add env y '()) (Add (Add env z '()) y '()) 
    pf = subAddTrans y (sing :: Sing '()) $ subWeaken (sing :: Sing env) z

class KnownFM f α => KnownD f α α' where
  fromD :: Value f (D (WRTFunctor f) α) -> α'

class KnownFM f α => KnownD' f α α' env where
  fromD' :: Interp f env (D (WRTFunctor f) α) -> α'
instance (KnownFM f α, KnownD f α α', Functor f, SingI env) 
      => KnownD' f α α' env where
  fromD' = fromD @f @α @α'. equivCoerce @f (wsD SWrtFunctor $ emptyDom @f @α) 
                                           (equivEmpty @env @EmptyT)

instance KnownFM IO a => KnownD IO (IO a) a where fromD = fromFM @IO
instance KnownD f () Void where fromD = id
instance KnownD f Void Void where fromD = id
instance (KnownD f α α', KnownD f β β') => KnownD f (α,β) (Either (α',β) (α,β'))
  where
    fromD (Left  (a',b)) = Left  (fromD @f @α a', fromFM @f b)
    fromD (Right (a,b')) = Right (fromFM @f a, fromD @f @β b')
instance (KnownD f α α', KnownD f β β') => KnownD f (Either α β) (Either α' β')
  where
    fromD (Left  a) = Left  $ fromD @f @α a
    fromD (Right b) = Right $ fromD @f @β b

-- Is the outermost Mu the left list or the right list?
-- I'm assuming left...
-- D' (Mu y (One :+: a :×: y))
-- =  Mu z. Zero :+: D' WrtFunctor a :×: [a] :+: a :×: Zero 
--      :+: (Zero :+: Zero :×: [a] :+: a :×: One) :×: z
-- ≅  Mu z. D' WrtFunctor a :×: [a] :+: a :×: z
instance (Functor f, KnownD f α α') => KnownD f [α] ([α],α',[α]) 
  where
    fromD e = (fromFM @f <$> pre, fromD @f @α @α' a, fromFM @f <$> post)
      where
--        e' :: ([Value f (ToFM (Just f) α)], Value f (D (WRTFunctor f) α)
--              ,[Value f (ToFM (Just f) α)])
        (pre,a,post) = fromDList @f @EmptyT @Z @(ToFM (Just f) α) $ e

{-
    fromD (Con (Left (Left x))) = case x of 
    fromD (Con (Left (Right (Left (a,ls))))) = ([],a',ls')
      where
        a' :: α'
        a' = withSingI env' $
             fromD' @f @α @α' @(AddT (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                     (D (WRTFunctor f) [α])) Z (ToFM (Just f) [α]))
             a
        ls' :: [α]
        ls' = withSingI env $
              fromFM' @f @(SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                (D (WRTFunctor f) [α]))
              $ case pf of Dict -> ls

        pf :: Dict (LookupT (AddT (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                  (D (WRTFunctor f) [α])) Z (ToFM (Just f) [α]))
                    Z ~ Just '(SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                  (D (WRTFunctor f) [α])
                              , ToFM (Just f) [α]))
        pf = unsafeCoerce (Dict :: Dict ())

        t :: Sing (ToFM (Just f) [α])
        t = sing
        t' :: Sing (D (WRTFunctor f) [α])
        t' = sD SWrtFunctor t


        env' :: Sing (AddT (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                               (D (WRTFunctor f) [α])) Z (ToFM (Just f) [α]))
        env' = addT env SZ t
        env :: Sing (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                (D (WRTFunctor f) [α]))
        env = singletonMapT (sFreshFor t) $ t'

    fromD (Con (Left (Right (Right (_, x))))) = case x of
    fromD (Con (Right (Left x,_))) = case x of
    fromD (Con (Right (Right (Left (x,_)),_))) = -- x has type D' y (ToFM α)
       error $ "Passed a value whose type should be Void"
    fromD (Con (Right (Right (Right (a,())),ls))) = case z' of
      (pre,v,post) -> (pre,v,a':post)
      where 
        a' :: α
        a' = withSingI env' $
             fromFM' @f @(AddT (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                               (D (WRTFunctor f) [α])) Z (ToFM (Just f) [α]))
             a
        z' :: ([α],α',[α])
        z' = fromD' @f @[α] @_ @EmptyT $ case pf of Dict -> ls

        pf :: Dict (LookupT (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                           (D (WRTFunctor f) [α])) 
                            (FreshFor (ToFM (Just f) [α])) 
                    ~ Just '(EmptyT, D (WRTFunctor f) [α]))
        pf = unsafeCoerce (Dict :: Dict ())


        t :: Sing (ToFM (Just f) [α])
        t = sing
        t' :: Sing (D (WRTFunctor f) [α])
        t' = sD SWrtFunctor t

        env' :: Sing (AddT (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                               (D (WRTFunctor f) [α])) Z (ToFM (Just f) [α]))
        env' = addT env SZ t

        env :: Sing (SingletonMapT (FreshFor (ToFM (Just f) [α])) 
                                (D (WRTFunctor f) [α]))
        env = singletonMapT (sFreshFor t) $ t'
-}

type FMList x t = Mu x (One :+: (t :×: Var x))

toFMList :: [Interp f env t] -> Interp f env (FMList x t)
toFMList = undefined
fromFMList :: Interp f env (FMList x t) -> [Interp f env t]
fromFMList = undefined

fromDList :: forall f env x t. Interp f env (D' WrtFunctor (FMList x t)) 
          -> ([Interp f env t], Interp f env (D' WrtFunctor t), [Interp f env t])
fromDList (Con (Left (Left x))) = case x of 
fromDList (Con (Left (Right (Left (a,ls))))) = ([],a',ls')
  where
    a' :: Interp f env (D' WrtFunctor t)
    a' = undefined -- equivCoerce @f @_ @env @_ @(D' WrtFunctor t) _ _ a

    ls' :: [Interp f env t]
    ls' = undefined
--        ls' = withSingI env $
--              fromFM' @f @(SingletonMapT x (D' WrtFunctor (FMList t)))
--              $ case pf of Dict -> ls

    pf :: Dict (LookupT (AddT (AddT env (FreshFor (FMList x t)) 
                                  (D' WrtFunctor (FMList x t))) 
                                  x (FMList x t))
                    x ~ Just '(AddT env (FreshFor (FMList x t))
                                        (D' WrtFunctor (FMList x t))
                              , FMList x t))
    pf = unsafeCoerce (Dict :: Dict ())
fromDList (Con (Left (Right (Right (_, x))))) = case x of
fromDList (Con (Right (Left x,_))) = case x of
fromDList (Con (Right (Right (Left (x,_)),_))) = -- x has type D' y (ToFM α)
   error $ "Passed a value whose type should be Void"
fromDList (Con (Right (Right (Right (a,_)),ls))) = case ls' of
  (pre,v,post) -> (pre,v,a':post)
  where 
    a' :: Interp f env t
    a' = undefined

    ls' :: ([Interp f env t],Interp f env (D' WrtFunctor t), [Interp f env t])
    ls' = undefined
--        ls' = withSingI env $
--              fromFM' @f @(SingletonMapT x (D' WrtFunctor (FMList t)))
--              $ case pf of Dict -> ls


