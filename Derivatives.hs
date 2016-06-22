{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, GADTs,
             DataKinds, PolyKinds,
             TypeInType, AllowAmbiguousTypes, TypeApplications #-}
{-# OPTIONS_GHC -Wall #-}

module Derivatives where

import GHC.TypeLits
import Data.Proxy
import Data.Type.Equality
import Data.Kind hiding (Type)
import GHC.Generics hiding (C, D, prec)

import Compat

--------------------------------------------------------------------------------

type family Lookup (assocs :: [(k,v)]) (def :: v) (needle :: k) :: v where
  Lookup '[]                          def needle = def
  Lookup ('(key,    value) ': assocs) def needle = If (key==needle) value (Lookup assocs def needle)

type family Append (assocs1 :: [(k,v)]) (assocs2 :: [(k,v)]) :: [(k,v)] where
    Append '[]             assocs2 = assocs2
    Append (kv ': assocs1) assocs2 = kv ': (Append assocs1 assocs2)

type family If (c :: Bool) (t :: k) (f :: k) :: k where
  If 'True  t f = t
  If 'False t f = f

type family (a :: Bool) || (b :: Bool) :: Bool where
  'True  || b = 'True
  'False || b = b

type Succ (n :: Nat) = 1 + n

type Max (m :: Nat) (n :: Nat) = If (m <=? n) n m

--------------------------------------------------------------------------------
-- Term level representations of types -----------------------------------------
--------------------------------------------------------------------------------

-- TODO: Add @Prim@ constructor
-- TODO: Automatic @Prim@
data Type' id = Var id
              | Zero | One
              | Type' id :+: Type' id | Type' id :×: Type' id
              | Mu id (Type' id)
              | Functorial (Type' id)
              deriving (Eq, Ord, Show, Read, Generic)
infixr 6 :+:
infixr 7 :×:

type Type = Type' Nat

--------------------------------------------------------------------------------
-- Term level representations of type variables --------------------------------
--------------------------------------------------------------------------------

data SourcedVar = User Nat | Generated Nat deriving Generic

type family (sv1 :: SourcedVar) `EqSourcedVar` (sv2 :: SourcedVar) :: Bool where
  'User      u1 `EqSourcedVar` 'User      u2 = u1 == u2
  'Generated g1 `EqSourcedVar` 'Generated g2 = g1 == g2
  'User      u1 `EqSourcedVar` 'Generated g2 = 'False
  'Generated g1 `EqSourcedVar` 'User      u2 = 'False

type instance (sv1 :: SourcedVar) == (sv2 :: SourcedVar) = sv1 `EqSourcedVar` sv2

data    ID  x
newtype Var x = VAR (ID x) deriving Generic

-- SuccMaxUserVar t : returns an upper bound on user variables in t
type family SuccMaxUserVar (t :: Type' SourcedVar) :: Nat where
  SuccMaxUserVar ('Var ('User x))       = Succ x
  SuccMaxUserVar ('Var ('Generated x))  = 0
  SuccMaxUserVar 'Zero                  = 0
  SuccMaxUserVar 'One                   = 0
  SuccMaxUserVar (s ':+: t)             = Max (SuccMaxUserVar s) (SuccMaxUserVar t)
  SuccMaxUserVar (s ':×: t)             = Max (SuccMaxUserVar s) (SuccMaxUserVar t)
  SuccMaxUserVar ('Mu ('User x) t)      = Max (Succ x)           (SuccMaxUserVar t)
  SuccMaxUserVar ('Mu ('Generated x) t) = SuccMaxUserVar t
  SuccMaxUserVar ('Functorial t)        = SuccMaxUserVar t

-- CollapseVars' u t : collapses all user and generated variables into flat
--                     natural numbers, by shifting the generated variables by
--                     u.
--                     PRECONDITION: u is an upper bound on the user variables
--                     in t
type family CollapseVars' (u :: Nat) (t :: Type' SourcedVar) :: Type where
  CollapseVars' u ('Var ('User x))       = 'Var x
  CollapseVars' u ('Var ('Generated x))  = 'Var (u + x)
  CollapseVars' u 'Zero                  = 'Zero
  CollapseVars' u 'One                   = 'One
  CollapseVars' u (s ':+: t)             = CollapseVars' u s ':+: CollapseVars' u t
  CollapseVars' u (s ':×: t)             = CollapseVars' u s ':×: CollapseVars' u t
  CollapseVars' u ('Mu ('User x) t)      = 'Mu x (CollapseVars' u t)
  CollapseVars' u ('Mu ('Generated x) t) = 'Mu (u + x) (CollapseVars' u t)
  CollapseVars' u ('Functorial t)        = 'Functorial (CollapseVars' u t)

-- CollapseVars t : collapses all user and generated variables into flat natural
--                  numbers.
type CollapseVars (t :: Type' SourcedVar) = CollapseVars' (SuccMaxUserVar t) t

--------------------------------------------------------------------------------
-- Type level operations on type variables -------------------------------------
--------------------------------------------------------------------------------

type family Subst (x :: id) (s :: Type' id) (t :: Type' id) :: Type' id where
  Subst x s ('Var y)        = If (x==y) s ('Var y)
  Subst x s 'Zero           = 'Zero
  Subst x s 'One            = 'One
  Subst x s (t1 ':+: t2)    = Subst x s t1 ':+: Subst x s t2
  Subst x s (t1 ':×: t2)    = Subst x s t1 ':×: Subst x s t2
  Subst x s ('Mu y t)       = If (x==y) ('Mu x t) ('Mu y (Subst x s t))
  Subst x s ('Functorial t) = 'Functorial (Subst x s t)

type family (x :: id) `FreeIn` (t :: Type' id) :: Bool where
  x `FreeIn` 'Var y        =  x == y
  x `FreeIn` 'Zero         = 'False
  x `FreeIn` 'One          = 'False
  x `FreeIn` (s ':+: t)    = (x `FreeIn` s) || (x `FreeIn` t)
  x `FreeIn` (s ':×: t)    = (x `FreeIn` s) || (x `FreeIn` t)
  x `FreeIn` 'Mu y t       = If (x==y) 'False (x `FreeIn` t)
  x `FreeIn` 'Functorial t = x `FreeIn` t

-- MaybeMu x t : returns a type equivalent to (Mu x.t). If x is not free in t,
--               (Mu x.t) is equivalent to t.
type MaybeMu (x :: id) (t :: Type' id) = If (x `FreeIn` t) ('Mu x t) t

-- FreshFor t : returns a type-level nat that is an upper bound on the variables
--              in t.
type family FreshFor (t :: Type) :: Nat where
  FreshFor ('Var x)        = Succ x
  FreshFor 'Zero           = 0
  FreshFor 'One            = 0
  FreshFor (s ':+: t)      = Max (FreshFor s) (FreshFor t)
  FreshFor (s ':×: t)      = Max (FreshFor s) (FreshFor t)
  FreshFor ('Mu x t)       = Max (Succ x)     (FreshFor t)
  FreshFor ('Functorial t) = FreshFor t

--------------------------------------------------------------------------------

-- Fresh env : returns an upper bound on the variables stored in env.
--             INVARIANT : The environment is alays stored with the largest
--                         variable at the head.
type family Fresh (env :: [(★, Nat)]) :: Nat where
  Fresh '[]              = 0
  Fresh ('(t,x) ': env') = Succ x

type Insert (t :: ★) (env :: [(★, Nat)]) = '(t, Fresh env) ': env

--------------------------------------------------------------------------------

-- 'ConvType'' is mostly straightforward.  The challenge is handling the 'Rec0'
-- case.  We maintain a binding from "types we're translating" to "their
-- variable" for use in 'Mu's.  Then, in the recursive case, we:
--
-- 1. Check to see if the type we're translating has been bound.  If it has,
--    insert its variable.  Otherwise:
-- 2. Give this type a fresh name, and then bind it in a @Mu@ if necessary.
--
-- We have to pass in the environment twice to 'ConvTypeRec'' so that we can
-- reuse the original environment after looping through it destructively.

-- We have to use an equality test here because the @D1Var@ and @C1_0Var@ types
-- we want to pattern-match on don't actually exist, somehow.
type family ConvTypeVariable' (mf :: Maybe (★ -> ★)) (env :: [(★, Nat)]) (f :: ★ -> ★) :: Type' SourcedVar where
  ConvTypeVariable' mf env (D1 d (C1 c (S1 NoSelector (Rec0 (ID x))))) =
    If ((D1 d (C1 c (S1 NoSelector (Rec0 (ID x))))) == Rep (Var x))
       ('Var ('User x))
       (ConvType' mf env (Rep (ID x)))
  ConvTypeVariable' mf env (M1 i c f) =
    ConvType' mf env f

type family ConvType' (mf :: Maybe (★ -> ★)) (env :: [(★, Nat)]) (f :: ★ -> ★) :: Type' SourcedVar where
  ConvType' mf env (M1 i c f) = ConvTypeVariable' mf env (M1 i c f)
  ConvType' mf env V1         = 'Zero
  ConvType' mf env U1         = 'One
  ConvType' mf env (f :+: g)  = ConvType' mf env f ':+: ConvType' mf env g
  ConvType' mf env (f :*: g)  = ConvType' mf env f ':×: ConvType' mf env g
  ConvType' mf env (Rec0 t)   = ConvTypeRec' mf env env t
  -- TODO: @ConvType' mf env (Rec0 Int)@ cases for weirdly recursive built-in types

type family ConvTypeRec' (mf :: Maybe (★ -> ★)) (env0 :: [(★, Nat)]) (env :: [(★, Nat)]) (t :: ★) :: Type' SourcedVar where
  ConvTypeRec' mf env0 '[]               t = ConvTypeMu' mf env0 t
  ConvTypeRec' mf env0 ('(t,  x) ': env) t = 'Var ('Generated x)
  ConvTypeRec' mf env0 ('(t', x) ': env) t = ConvTypeRec' mf env0 env t

type family ConvTypeMu' (mf :: Maybe (★ -> ★)) (env :: [(★, Nat)]) (t :: ★) :: Type' SourcedVar where
  ConvTypeMu' ('Just f) env (f t) = 'Functorial (ConvTypeMu' ('Just f) env t)
  ConvTypeMu' mf        env t      = MaybeMu ('Generated (Fresh env)) (ConvType' mf (Insert t env) (Rep t))
-- This always ticks the variable count by 1, so some IDs are unused.

-- ConvType t :: Type
--              produces a type-level representation of the Haskell type t
type ConvType (mf :: Maybe (★ -> ★)) (t :: ★) = CollapseVars (ConvTypeMu' mf '[] t)

-- TODO Potential bug:
-- 
-- >>> :k! ConvType 'Nothing ([Var X],[Var X])
-- ConvType 'Nothing ([Var X],[Var X]) :: Type
-- = 'Mu 2 ('One ':+: ('Var 0 ':×: 'Var 2))
--   ':×: 'Mu 2 ('One ':+: ('Var 0 ':×: 'Var 2))
--
-- Note the reuse of @2@.  That may not be bad – we may have a guarantee they'll
-- always occur at different scopes – but I'd like to convince myself of that.


--------------------------------------------------------------------------------
-- DERIVATIVES -----------------------------------------------------------------
--------------------------------------------------------------------------------

data Wrt' = WrtVar' Nat | WrtFunctor' deriving Generic

-- D' x t : partial derivative of t with respect to x
type family D' (x :: Wrt') (t :: Type) :: Type where
  D' ('WrtVar' x) ('Var y)        = If (x==y) 'One 'Zero
  D' 'WrtFunctor' ('Var y)        = 'Zero
  D' wx           'Zero           = 'Zero
  D' wx           'One            = 'Zero
  D' wx           (s ':+: t)      = D' wx s ':+: D' wx t
  D' wx           (s ':×: t)      = (D' wx s ':×: t) ':+: (s ':×: D' wx t)
  D' ('WrtVar' x) ('Mu y t)       = If (x==y) 'Zero 
                                              (DMu ('WrtVar' x) (FreshFor ('Mu y t)) y t)
  D' 'WrtFunctor' ('Mu y t)       = DMu 'WrtFunctor' (FreshFor ('Mu y t)) y t
  D' ('WrtVar' x) ('Functorial t) = 'Zero
  D' 'WrtFunctor' ('Functorial t) = t

type DMu (wx :: Wrt') (z :: Nat) (y :: Nat) (t :: Type) =
  'Mu z (DMu' wx z y t)
type DMu' (wx :: Wrt') (z :: Nat) (y :: Nat) (t :: Type) =
        (Subst y ('Mu y t) (D' wx t)
        ':+: (Subst y ('Mu y t) (D' ('WrtVar' y) t) ':×: 'Var z))

-- Simplify1 t : produces a type-level Type that is simplified based on simple
--               arithmetic. 

type family Simplify1 (t :: Type' id) :: Type' id where
  Simplify1 ('Zero ':+: t) = Simplify1 t
  Simplify1 (t ':+: 'Zero) = Simplify1 t
  
  Simplify1 ('One ':×: t) = Simplify1 t
  Simplify1 (t ':×: 'One) = Simplify1 t
  
  Simplify1 ('Zero ':×: t) = 'Zero
  Simplify1 (t ':×: 'Zero) = 'Zero

  Simplify1 (a ':+: b)      = Simplify1 a ':+: Simplify1 b
  Simplify1 (a ':×: b)      = Simplify1 a ':×: Simplify1 b
  Simplify1 ('Mu x t)       = 'Mu x (Simplify1 t)
  Simplify1 ('Functorial t) = 'Functorial (Simplify1 t)
  
  Simplify1 t = t

-- FixSimplify t t' : if the fixpoint has converged (t=t'), returns t;
--                    otherwise, call simplify
type family FixSimplify (t :: Type' id) (t' :: Type' id) :: Type' id where
  FixSimplify t t  = t
  FixSimplify t t' = Simplify t'

-- Simplify t : Computes the fixpoint of Simplify1 
type Simplify t = FixSimplify t (Simplify1 t)

data Wrt a = WrtVar Nat | WrtFunctor a

-- D x a : Converts a Haskell type a into a type-level Type
type family D (x :: Wrt (★ -> ★)) (a :: ★) :: Type where
  D ('WrtVar     x) a = Simplify (D' ('WrtVar' x) (ConvType 'Nothing  a))
  D ('WrtFunctor f) a = Simplify (D' 'WrtFunctor' (ConvType ('Just f) a))

-- DWrt x a : Converts a Haskell type a into a type-level Type
type family DWrt (x :: k) (a :: ★) :: Type where
  DWrt (x :: Nat)    a = D ('WrtVar x)     a
  DWrt (f :: ★ -> ★) a = D ('WrtFunctor f) a

--------------------------------------------------------------------------------
-- Term-level Types ------------------------------------------------------------
--------------------------------------------------------------------------------

-- Converts a type-level Type to a term-level Type
class KnownType (t :: Type) where
  typeVal :: Type' Integer

instance KnownNat x => KnownType ('Var x) where
  typeVal = Var $ natVal (Proxy :: Proxy x)

instance KnownType 'Zero where
  typeVal = Zero

instance KnownType 'One where
  typeVal = One

instance (KnownType s, KnownType t) => KnownType (s ':+: t) where
  typeVal = typeVal @s :+: typeVal @t

instance (KnownType s, KnownType t) => KnownType (s ':×: t) where
  typeVal = typeVal @s :×: typeVal @t

instance (KnownNat x, KnownType t) => KnownType ('Mu x t) where
  typeVal = Mu (natVal (Proxy :: Proxy x)) (typeVal @t)

instance KnownType t => KnownType ('Functorial t) where
  typeVal = Functorial (typeVal @t)

-- freeIn x t : Term-level free variables
freeIn :: Eq a => a -> Type' a -> Bool
x `freeIn` Var y        = x == y
_ `freeIn` Zero         = False
_ `freeIn` One          = False
x `freeIn` (s :+: t)    = (x `freeIn` s) || (x `freeIn` t)
x `freeIn` (s :×: t)    = (x `freeIn` s) || (x `freeIn` t)
x `freeIn` Mu y t       = x /= y && (x `freeIn` t)
x `freeIn` Functorial t = x `freeIn` t

--------------------------------------------------------------------------------
-- Pretty Printing -------------------------------------------------------------
--------------------------------------------------------------------------------

prettyVar :: Integer -> String
prettyVar x = maybe ('x' : map subscript (show $ x-26)) pure
            $ lookup x (zip [0..] $ "xyz" ++ ['a'..'w'])
  where
    subscript '0' = '₀'
    subscript '1' = '₁'
    subscript '2' = '₂'
    subscript '3' = '₃'
    subscript '4' = '₄'
    subscript '5' = '₅'
    subscript '6' = '₆'
    subscript '7' = '₇'
    subscript '8' = '₈'
    subscript '9' = '₉'
    subscript c   = c

prettyType :: Type' Integer -> String
prettyType = go (0 :: Word) where
  prod_prec, sum_prec, app_prec, top_prec :: Word
  app_prec  = 3
  prod_prec = 2
  sum_prec  = 1
  top_prec  = 0
  
  go prec (Mu x (t :+: (s :×: Var y)))
    | x == y && not (x `freeIn` t) && not (x `freeIn` s)
    = let list = "[" ++ go top_prec s ++ "]"
      in if t == One
         then list
         else parens (prec > prod_prec) $ list ++ " × " ++ go prod_prec t
  
  go _    (Var x)        = prettyVar x
  go _    Zero           = "𝟎"
  go _    One            = "𝟏"
  go prec (s :+: t)      = parens (prec > sum_prec)  $ go sum_prec s ++ " + " ++ go sum_prec t
  go prec (s :×: t)      = parens (prec > prod_prec) $ go prod_prec s ++ " × " ++ go prod_prec t
  go prec (Mu x t)       = parens (prec > top_prec)  $ "μ" ++ prettyVar x ++ ". " ++ go top_prec t
  go prec (Functorial t) = "⋄" ++ parens (prec > app_prec) (go app_prec t)

  parens True  = ("(" ++) . (++ ")")
  parens False = id

--------------------------------------------------------------------------------
-- Type Variables --------------------------------------------------------------
--------------------------------------------------------------------------------

type X = 0
type Y = 1
type Z = 2
type A = 3
type B = 4
type C = 5

--------------------------------------------------------------------------------

data Tree a = Leaf a | Node (Tree a) (Tree a) deriving (Eq, Ord, Read, Show, Generic)

data Rose a = Rose a [Rose a] deriving (Eq, Ord, Read, Show, Generic)
