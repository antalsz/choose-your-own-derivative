{-# LANGUAGE KindSignatures, PolyKinds, TypeOperators, DataKinds,
             TypeFamilies, GADTs, UndecidableInstances, RankNTypes,
             AllowAmbiguousTypes, ConstraintKinds, ScopedTypeVariables,
             TypeApplications, InstanceSigs, MultiParamTypeClasses,
             FlexibleInstances, FunctionalDependencies, TypeInType, EmptyCase,
             StandaloneDeriving
#-}
{-# OPTIONS_GHC -Wall -fno-warn-unticked-promoted-constructors #-}

module Constraints where

import Data.Constraint
import Data.Type.Equality
import Unsafe.Coerce
import Data.Singletons
import Data.Singletons.Prelude.Maybe
import Data.Singletons.Prelude.Tuple
import Data.Kind (type (*))
import Data.Typeable (Proxy(..))

-- Nats
data Nat = Z | S Nat

instance Eq Nat where
  Z == Z   = True
  Z == S _ = False
  S _ == Z = False
  S m == S n = (m == n)
type instance Z == Z= True
type instance Z == S _ = False
type instance S _ == Z = False
type instance S m == S n = m == n

type family Max (m :: Nat) (n :: Nat) :: Nat where
  Max 'Z     n      = n
  Max ('S m) 'Z     = 'S m
  Max ('S m) ('S n) = 'S (Max m n)

sMax :: Sing m -> Sing n -> Sing (Max m n)
sMax SZ     n = n
sMax (SS m) SZ = SS m
sMax (SS m) (SS n) = SS $ sMax m n

type family (m :: Nat) >= (n :: Nat) :: Bool where
  Z   >= Z   = True
  S _ >= Z   = True
  Z   >= S _ = False
  S m >= S n = m >= n

type family Or b1 b2 where
  Or True  _     = True
  Or _     True  = True
  Or False False = False

type family (m :: Nat) + (n :: Nat) :: Nat where
  Z   + n = n
  S m + n = S (m + n)

--data NEq (m :: Nat) (n :: Nat) where
  -- TODO

eqEq :: forall (x :: Nat) y. ((x == y) ~True) => Sing x -> Sing y -> Dict (x ~ y)
eqEq SZ     SZ     = Dict
eqEq (SS x) (SS y) = case eqEq x y of Dict -> Dict

eqSuccFalse :: forall (n :: Nat).
               Sing n -> Dict ((S n==n) ~ 'False, (n==S n) ~ 'False)
eqSuccFalse SZ     = Dict
eqSuccFalse (SS n) = eqSuccFalse n

eqRefl :: Sing (n :: Nat) -> Dict ((n==n)~'True)
eqRefl SZ = Dict
eqRefl (SS n) = case eqRefl n of Dict -> Dict


geRefl :: Sing (n :: Nat) -> Dict ((n >= n) ~ True)
geRefl SZ = Dict
geRefl (SS n) = geRefl n

succGeTrue :: (x >= S y) ~ True => Sing x -> Sing y -> Dict ((x == y) ~ False, (y == x) ~ False)
succGeTrue (SS _) SZ     = Dict
succGeTrue (SS x) (SS y) = succGeTrue x y

maxSymm :: Sing m -> Sing n -> Dict (Max m n ~ Max n m)
maxSymm SZ     SZ     = Dict
maxSymm (SS _) SZ     = Dict
maxSymm SZ     (SS _) = Dict
maxSymm (SS m) (SS n) = case maxSymm m n of Dict -> Dict

maxGeTrans :: (x >= Max m n ~ True) => Sing x -> Sing m -> Sing n -> Dict (x >= m ~ True, x >= n ~ True)
maxGeTrans SZ SZ SZ = Dict
maxGeTrans (SS _) SZ SZ = Dict
maxGeTrans SZ (SS _) m = case m of
maxGeTrans (SS _) (SS _) SZ = Dict
maxGeTrans (SS _) SZ (SS _) = Dict
maxGeTrans (SS x) (SS m) (SS n) = maxGeTrans x m n

geEqFalse :: x >= S y ~ True => Sing x -> Sing y -> Dict ((x == y) ~ False)
geEqFalse (SS _) SZ     = Dict
geEqFalse (SS x) (SS y) = geEqFalse x y


-- SNats --------------------------------------------------------

data instance Sing (n :: Nat) where
  SZ :: Sing 'Z
  SS :: Sing n -> Sing ('S n)

deriving instance Show (Sing (n :: Nat))

instance SingI Z where sing = SZ
instance SingI n => SingI (S n) where sing = SS sing

compareSNat :: forall (m :: Nat) (n :: Nat). Sing m -> Sing n -> Bool
compareSNat SZ     SZ     = True
compareSNat (SS m) (SS n) = compareSNat m n
compareSNat _       _     = False


withDict :: Dict c -> (c => r) -> r
withDict Dict r = r


type family IfEqNat (x :: Nat) (y :: Nat) (t :: k) (f :: k) :: k where
  IfEqNat x x t _ = t
  IfEqNat _ _ _ f = f

ifEqNat :: forall (x :: Nat) (y :: Nat) (r :: *).
           Sing x -> Sing y
        -> (((x == y) ~ 'True, x ~ y) => r)
        -> (((x == y) ~ 'False, (y==x) ~ 'False) => r)
        -> r
ifEqNat x y t f | compareSNat x y = isTrue t
                | otherwise       = isFalse f
  where isTrue :: (((x == y) ~ 'True, x ~ y) => r) -> r
        isTrue = withDict ((unsafeCoerce :: Dict ((),()) -> Dict ((x == y) ~ 'True, x ~ y)) Dict)

        isFalse :: (((x == y) ~ 'False, (y==x) ~ 'False) => r) -> r
        isFalse = withDict ((unsafeCoerce :: Dict ((),()) -> Dict (((x == y) ~ 'False), (y == x) ~ 'False)) Dict)




-- Type-level maps indexed by Nats ------------------------------

data Ctx   a = Empty | N (NCtx a)
data NCtx  a = End a | Cons (Maybe a) (NCtx a)

-- Singleton contexts

data instance Sing (g :: Ctx a) where
  SEmpty :: Sing Empty
  SN     :: Sing g -> Sing (N g)
data instance Sing (g :: NCtx a) where
  SEnd  :: Sing a -> Sing (End a)
  SCons :: Sing u -> Sing g -> Sing (Cons u g)

instance SingI Empty where sing = SEmpty
instance SingI g => SingI (N g) where sing = SN sing

instance SingI a => SingI (End a) where sing = SEnd sing
instance (SingI u, SingI g) => SingI (Cons u g) where
  sing = SCons sing sing


class FinMap (map :: * -> *) where

  type Lookup (ctx :: map a) (i :: Nat) :: Maybe a
  type Add (ctx :: map a) (x :: Nat) (v :: a) :: map a
  type SingletonMap (x :: Nat) (v :: a) :: map a

  add :: Sing (ctx :: map a) -> Sing (x :: Nat) -> Sing (v :: a)
      -> Sing (Add ctx x v)

  singletonMap :: Sing (x :: Nat) -> Sing (v :: a)
               -> Sing (SingletonMap x v :: map a)

  lookupAddEq :: Sing (env :: map α) -> Sing x -> Proxy (a :: α)
              -> Dict (Lookup (Add env x a) x ~ Just a)

  lookupAddNEq :: ((x==y) ~ 'False)
               => Sing (env :: map α) -> Sing x -> Sing y -> Proxy s
               -> Dict (Lookup (Add env y s) x ~ Lookup env x)

  lookupSingletonEq :: Sing x -> Proxy (a :: α)
       -> Dict (Lookup (SingletonMap x a :: map α) x ~ Just a)

  lookupSingletonNEq :: forall a x y. ((x==y) ~ 'False)
                     => Sing x -> Sing y -> Proxy a
                     -> Dict (Lookup (SingletonMap y a :: map α) x ~ 'Nothing)

instance FinMap Ctx  where
  type Lookup Empty   _ = Nothing
  type Lookup (N ctx) i = Lookup ctx i

  type Add Empty   x v = SingletonMap x v
  type Add (N ctx) x v = N (Add ctx x v)

  type SingletonMap x v = N (SingletonMap x v)

  add SEmpty   x v = singletonMap x v
  add (SN ctx) x v = SN $ add ctx x v

  singletonMap x v = SN $ singletonMap x v

  lookupAddEq SEmpty   x a = lookupSingletonEq @Ctx x a
  lookupAddEq (SN ctx) x a = lookupAddEq ctx x a

  lookupAddNEq SEmpty   x y a = lookupSingletonNEq @Ctx x y a
  lookupAddNEq (SN ctx) x y a = lookupAddNEq ctx x y a

  lookupSingletonEq x a = lookupSingletonEq @NCtx x a

  lookupSingletonNEq x y a = lookupSingletonNEq @NCtx x y a



instance FinMap NCtx where
  type Lookup (End t)           Z       = Just t
  type Lookup (End t)           (S _)   = Nothing
  type Lookup (Cons u _)        Z       = u
  type Lookup (Cons _ ctx)      (S x)   = Lookup ctx x

  type Add (End _)      Z       v = End v
  type Add (End w)      (S x)   v = Cons (Just w) (SingletonMap x v)
  type Add (Cons _ ctx) Z       v = Cons (Just v) ctx
  type Add (Cons u ctx) (S x)   v = Cons u (Add ctx x v)

  add (SEnd _)      SZ     v = SEnd v
  add (SEnd a)      (SS x) v = SCons (SJust a) (singletonMap x v)
  add (SCons _ ctx) SZ     v = SCons (SJust v) ctx
  add (SCons u ctx) (SS x) v = SCons u (add ctx x v)

  type SingletonMap Z     v = End v
  type SingletonMap (S x) v = Cons Nothing (SingletonMap x v)

  singletonMap SZ     v = SEnd v
  singletonMap (SS x) v = SCons SNothing $ singletonMap x v

  lookupAddEq (SEnd _)      SZ     _ = Dict
  lookupAddEq (SEnd _)      (SS x) v = lookupSingletonEq @NCtx x v
  lookupAddEq (SCons _ _)   SZ     _ = Dict
  lookupAddEq (SCons _ ctx) (SS x) a = lookupAddEq ctx x a

  lookupAddNEq (SEnd _)      SZ     (SS _) _ = Dict
  lookupAddNEq (SEnd _)      (SS _) SZ     _ = Dict
  lookupAddNEq (SEnd _)      (SS x) (SS y) a = lookupSingletonNEq @NCtx x y a
  lookupAddNEq (SCons _ _)   SZ     (SS _) _ = Dict
  lookupAddNEq (SCons _ _)   (SS _) SZ     _ = Dict
  lookupAddNEq (SCons _ ctx) (SS x) (SS y) a = lookupAddNEq ctx x y a

  lookupSingletonEq SZ _ = Dict
  lookupSingletonEq (SS x) a = case lookupSingletonEq @NCtx x a of Dict -> Dict

  lookupSingletonNEq SZ (SS _) _ = Dict
  lookupSingletonNEq (SS _) SZ _ = Dict
  lookupSingletonNEq (SS x) (SS y) a = lookupSingletonNEq @NCtx x y a


-- Lists

type family Append (ls1 :: [k]) (ls2 :: [k]) :: [k] where
  Append '[] ls2 = ls2
  Append (a ': ls1) ls2= a ': (Append ls1 ls2)

---------------------------------------

-- Merge
 -- Merge -----------------------------------------

class Mergeable (a :: *) where
  type family Merge a (x :: a) (y :: a) :: a
  (⋓) :: Sing dom1 -> Sing dom2 -> Sing (Merge a dom1 dom2)

  mergeSymm :: Sing x -> Sing y -> Dict (Merge a x y ~ Merge a y x)


instance Mergeable a => Mergeable (Maybe a) where
  type Merge (Maybe a) m Nothing  = m
  type Merge (Maybe a) Nothing  m = m
  type Merge (Maybe a) (Just x) (Just y) = Just (Merge a x y)

  SNothing ⋓ SNothing = SNothing
  SJust a  ⋓ SNothing = SJust a
  SNothing ⋓ SJust a  = SJust a
  SJust a  ⋓ SJust b  = SJust (a ⋓ b)

  mergeSymm SNothing  SNothing  = Dict
  mergeSymm (SJust _) SNothing  = Dict
  mergeSymm SNothing  (SJust _) = Dict
  mergeSymm (SJust a) (SJust b) = case mergeSymm a b of Dict -> Dict

instance Mergeable () where
  type Merge () '() '() = '()
  STuple0 ⋓ STuple0 = STuple0
  mergeSymm STuple0 STuple0 = Dict

instance Mergeable a => Mergeable (NCtx a) where
  type Merge (NCtx a) (End x)      (End y)      = End (Merge a x y)
  type Merge (NCtx a) (End x)      (Cons m g)   = Cons (Merge (Maybe a) (Just x) m) g
  type Merge (NCtx a) (Cons m g)   (End x)      = Cons (Merge (Maybe a) m (Just x)) g
  type Merge (NCtx a) (Cons m1 g1) (Cons m2 g2) =
    Cons (Merge (Maybe a) m1 m2) (Merge (NCtx a) g1 g2)

  (SEnd a) ⋓ (SEnd b) = SEnd (a ⋓ b)
  (SEnd a1) ⋓ (SCons m2 g2) = SCons (SJust a1 ⋓ m2) g2
  (SCons m1 g1) ⋓ (SEnd a2) = SCons (m1 ⋓ SJust a2) g1
  SCons m1 g1 ⋓ SCons m2 g2 = SCons (m1 ⋓ m2) (g1 ⋓ g2)

  mergeSymm (SEnd a) (SEnd b) = case mergeSymm a b of Dict -> Dict
  mergeSymm (SEnd a) (SCons m _) = case mergeSymm (SJust a) m of Dict -> Dict
  mergeSymm (SCons m _) (SEnd b) = case mergeSymm m (SJust b) of Dict -> Dict
  mergeSymm (SCons m1 g1) (SCons m2 g2) =
    case mergeSymm m1 m2 of {Dict ->
    case mergeSymm g1 g2 of {Dict ->
    Dict }}

instance Mergeable a => Mergeable (Ctx a) where
  type Merge (Ctx a) Empty Empty = Empty
  type Merge (Ctx a) Empty (N g) = N g
  type Merge (Ctx a) (N g) Empty = N g
  type Merge (Ctx a) (N g1) (N g2) = N (Merge (NCtx a) g1 g2)

  SEmpty ⋓ SEmpty = SEmpty
  SEmpty ⋓ SN g   = SN g
  SN g   ⋓ SEmpty = SN g
  SN g1  ⋓ SN g2  = SN (g1 ⋓ g2)

  mergeSymm SEmpty SEmpty = Dict
  mergeSymm SEmpty (SN _) = Dict
  mergeSymm (SN _) SEmpty = Dict
  mergeSymm (SN g1) (SN g2) = case mergeSymm g1 g2 of Dict -> Dict



lookupMerge :: forall a (dom1 :: Ctx a) (dom2 :: Ctx a) (x :: Nat).
               Sing dom1 -> Sing dom2 -> Sing x
            -> Dict ( Lookup (Merge (Ctx a) dom1 dom2) x
                    ~ Merge (Maybe a) (Lookup dom1 x) (Lookup dom2 x) )
lookupMerge SEmpty SEmpty _ = Dict
lookupMerge SEmpty (SN _) _ = Dict
lookupMerge (SN _) SEmpty _ = Dict
lookupMerge (SN dom1) (SN dom2) x = lookupMergeN dom1 dom2 x

lookupMergeN :: forall a (dom1 :: NCtx a) (dom2 :: NCtx a) (x :: Nat).
               Sing dom1 -> Sing dom2 -> Sing x
            -> Dict ( Lookup (Merge (NCtx a) dom1 dom2) x
                    ~ Merge (Maybe a) (Lookup dom1 x) (Lookup dom2 x) )
lookupMergeN (SEnd _) (SEnd _)       SZ = Dict
lookupMergeN (SEnd _) (SEnd _)       (SS _) = Dict
lookupMergeN (SEnd _) (SCons _ _)    SZ = Dict
lookupMergeN (SEnd _) (SCons _ _)    (SS _) = Dict
lookupMergeN (SCons _ _) (SEnd _)    SZ = Dict
lookupMergeN (SCons _ _) (SEnd _)    (SS _) = Dict
lookupMergeN (SCons _ _) (SCons _ _) SZ = Dict
lookupMergeN (SCons _ ctx1) (SCons _ ctx2) (SS n) = lookupMergeN ctx1 ctx2 n

-- Remove Type Family

type family Remove (x :: Nat) (g :: Ctx a) :: Ctx a where
  Remove _ Empty = Empty
  Remove x (N g) = RemoveN x g
type family RemoveN (x :: Nat) (g :: NCtx a) :: Ctx a where
  RemoveN Z     (End s)    = Empty
  RemoveN (S _) (End s)    = N (End s)
  RemoveN Z     (Cons _ g) = N (Cons Nothing g)
  RemoveN (S x) (Cons u g) = Cons' u (RemoveN x g)

remove :: Sing x -> Sing g -> Sing (Remove x g)
remove _ SEmpty = SEmpty
remove x (SN g) = removeN x g

removeN :: Sing x -> Sing g -> Sing (RemoveN x g)
removeN SZ     (SEnd _)    = SEmpty
removeN (SS _) (SEnd s)    = SN $ SEnd s
removeN SZ     (SCons _ g) = SN $ SCons SNothing g
removeN (SS x) (SCons u g) = sCons u $ removeN x g


type family Cons' (u :: Maybe a) (g :: Ctx a) :: Ctx a where
  Cons' Nothing Empty = Empty
  Cons' (Just x) Empty = N (End x)
  Cons' u (N g) = N (Cons u g)

sCons :: Sing u -> Sing g -> Sing (Cons' u g)
sCons SNothing SEmpty = SEmpty
sCons (SJust x) SEmpty = SN $ SEnd x
sCons u         (SN g) = SN $ SCons u g

lookupRemove :: Sing x -> Sing g -> Dict (Lookup (Remove x g) x ~ Nothing)
lookupRemove _ SEmpty = Dict
lookupRemove x (SN g) = lookupRemoveN x g

lookupRemoveN :: Sing x -> Sing g -> Dict (Lookup (RemoveN x g) x ~ Nothing)
lookupRemoveN SZ     (SEnd _)    = Dict
lookupRemoveN (SS _) (SEnd _)    = Dict
lookupRemoveN SZ     (SCons _ _) = Dict
lookupRemoveN (SS x) (SCons u g) = case lookupRemoveN x g of {Dict ->
                                   case lookupCons' x u (removeN x g) of {Dict -> Dict}}

lookupRemoveNEq :: (x == y) ~ False
                => Sing x -> Sing y -> Sing g 
                -> Dict (Lookup (Remove y g) x ~ Lookup g x)
lookupRemoveNEq _ _ SEmpty = Dict
lookupRemoveNEq x y (SN γ) = lookupRemoveNNEq x y γ

lookupRemoveNNEq :: (x == y) ~ False
                 => Sing x -> Sing y -> Sing g 
                 -> Dict (Lookup (RemoveN y g) x ~ Lookup g x)
lookupRemoveNNEq (SS _) SZ     (SEnd _) = Dict
lookupRemoveNNEq _      (SS _) (SEnd _) = Dict
lookupRemoveNNEq (SS _) SZ     (SCons _ _) = Dict
lookupRemoveNNEq SZ     (SS y) (SCons u g) = lookupCons'Z u (removeN y g)
lookupRemoveNNEq (SS x) (SS y) (SCons u g) = 
  case lookupCons' x u (removeN y g) of Dict -> lookupRemoveNNEq x y g


lookupCons'Z :: Sing u -> Sing g -> Dict (Lookup (Cons' u g) Z ~ u)
lookupCons'Z SNothing  SEmpty = Dict
lookupCons'Z (SJust _) SEmpty = Dict
lookupCons'Z _         (SN _) = Dict

lookupCons' :: Sing x -> Sing u -> Sing g -> Dict (Lookup (Cons' u g) (S x) ~ Lookup g x)
lookupCons' _ SNothing  SEmpty = Dict
lookupCons' _ (SJust _) SEmpty = Dict
lookupCons' _ _         (SN _) = Dict

-- Proofs about the intersection of Add and Merge (and Singleton)



addMergeSingleton :: Sing γ -> Sing x
                  -> Dict (Add γ x '() ~ Merge (NCtx ()) (SingletonMap x '()) γ)
addMergeSingleton (SEnd STuple0) SZ = Dict
addMergeSingleton (SEnd STuple0) (SS _) = Dict
addMergeSingleton (SCons SNothing _)    SZ = Dict
addMergeSingleton (SCons (SJust STuple0) _) SZ = Dict
addMergeSingleton (SCons _ γ) (SS x) = case addMergeSingleton γ x of Dict -> Dict

addDistrL :: Sing g1 -> Sing g2 -> Sing x ->
    Dict (Add (Merge (Ctx ()) g1 g2) x '() ~ Merge (Ctx ()) (Add g1 x '()) g2)
addDistrL SEmpty SEmpty _ = Dict
-- Add ([] ⋓ N γ) x = Add (N γ) x
-- vs
-- (Add [] x) ⋓ N γ = (SingletonMap x) ⋓ N γ
addDistrL SEmpty (SN γ)   x = case addMergeSingleton γ x of Dict -> Dict
addDistrL (SN _)  SEmpty  _ = Dict
addDistrL (SN γ1) (SN γ2) x = case addNDistrL γ1 γ2 x of Dict -> Dict

addNDistrL :: Sing g1 -> Sing g2 -> Sing x ->
    Dict (Add (Merge (NCtx ()) g1 g2) x '() ~ Merge (NCtx ()) (Add g1 x '()) g2)
addNDistrL (SEnd STuple0) (SEnd STuple0)            SZ = Dict
addNDistrL (SEnd STuple0) (SEnd STuple0)            (SS _) = Dict
addNDistrL (SEnd STuple0) (SCons SNothing _)        SZ = Dict
addNDistrL (SEnd STuple0) (SCons (SJust STuple0) _) SZ = Dict
-- End () ⋓ u :: γ = (Just () ⋓ u) :: γ
-- Add ^ (SS x) = (Just () ⋓ u) :: Add γ x
-- vs 
-- (Add (End ()) (S x)) ⋓ (u :: γ)
-- = (Just () :: SingletonMap x ()) ⋓ (u :: γ)
-- = (Just () ⋓ u) :: (SingletonMap x () ⋓ γ)
addNDistrL (SEnd STuple0) (SCons _ γ)               (SS x) = 
  case addMergeSingleton γ x of Dict -> Dict
addNDistrL (SCons _ _)    (SEnd STuple0)            SZ = Dict
addNDistrL (SCons _ _)    (SEnd STuple0)            (SS _) = Dict
--   Add ((u1 :: γ1) ⋓ (u2 :: γ2)) 0 
-- = Add ((u1 ⋓ u2) :: (γ1 ⋓ γ2)) 0
-- = (Just ()) :: γ1 ⋓ γ2
-- vs
--   (Add (u1 :: γ1) 0) ⋓ (u2 :: γ2)
-- = (Just () :: γ1) ⋓ (u2 :: γ2)
-- = (Just () ⋓ u2) :: γ1 ⋓ γ2
addNDistrL (SCons _ _)  (SCons u2 _)               SZ = case u2 of 
    SJust STuple0 -> Dict
    SNothing      -> Dict
--   Add ((u1 :: γ1) ⋓ (u2 :: γ2)) (S x)
-- = Add ((u1 ⋓ u2) :: (γ1 ⋓ γ2)) (S x)
-- = (u1 ⋓ u2) :: (Add (γ1 ⋓ γ2) x)
-- vs
--   (Add (u1 :: γ1) (S x)) ⋓ (u2 :: γ2)
-- = (u1 :: Add γ1 x) ⋓ (u2 :: γ2)
-- = (u1 ⋓ u2) :: (Add γ1 x ⋓ γ2)
addNDistrL (SCons _ γ1)  (SCons _ γ2)              (SS x) = 
  case addNDistrL γ1 γ2 x of Dict -> Dict

