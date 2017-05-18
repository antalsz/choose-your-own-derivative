{-# LANGUAGE KindSignatures, TypeOperators, PolyKinds, DataKinds,
             TypeFamilies,
             ScopedTypeVariables, AllowAmbiguousTypes, TypeApplications,
             BangPatterns #-}
{-# OPTIONS_GHC -Wall -Wno-unticked-promoted-constructors #-}

module Pretty where

import Types
import Constraints

import Data.Constraint
import Data.Singletons
import Data.Typeable
import Data.Char

--------------------------------------------------------------------------------
-- Pretty-printing -------------------------------------------------------------
--------------------------------------------------------------------------------

prettyType :: forall (t :: FMType' Nat). (TypeableFM t, SingI t) => String
prettyType = prettyType' (sing @_ @t)

printType :: forall (t :: FMType' Nat). (TypeableFM t, SingI t) => IO ()
printType = putStrLn $ prettyType @t

----------------------------------------

prettyVar :: forall (x :: Nat). Sing x -> String
prettyVar = go 0 where
  go :: forall (y :: Nat). Integer -> Sing y -> String
  go !n SZ     = prettyVar' n
  go !n (SS x) = go (n+1) x

prettyVar' :: Integer -> String
prettyVar' x
  | x < 0     = '_' : prettyVar' (-x)
  | otherwise = let offset o d = toEnum $ fromEnum o + fromIntegral d
                    (q,r)      = x `quotRem` 26
                    letter     = offset 'a' r
                    subscript | q == 0    = ""
                              | otherwise = map (offset '₀' . digitToInt) $ show q
              in letter : subscript

prettyType' :: forall (t :: FMType' Nat). TypeableFM t => Sing t -> String
prettyType' = go (0 :: Word) where
  prod_prec, sum_prec, app_prec, subst_prec, top_prec :: Word
  app_prec   = 4
  prod_prec  = 3
  sum_prec   = 2
  subst_prec = 1
  top_prec   = 0

  go :: forall (s :: FMType' Nat). TypeableFM s => Word -> Sing s -> String
  go prec (SMu x (t `SPlus` (s `STimes` SVar y)))
    | (x `compareSNat` y) && not (x `freeIn` t) && not (x `freeIn` s)
    = let list = "[" ++ go top_prec s ++ "]"
      in case t of
           SOne -> list
           _    -> parens (prec > prod_prec) $ list ++ " × " ++ go prod_prec t
  
  go _    (SVar x)        = prettyVar x
  go _    SZero           = "𝟎"
  go _    SOne            = "𝟏"
  go prec (s `SPlus` t)   = parens (prec > sum_prec)   $ go sum_prec s ++ " + " ++ go sum_prec t
  go prec (s `STimes` t)  = parens (prec > prod_prec)  $ go prod_prec s ++ " × " ++ go prod_prec t
  go prec (SMu x t)       = parens (prec > top_prec)   $ "μ" ++ prettyVar x ++ ". " ++ go top_prec t
  go prec (SSubst s x t)  = parens (prec > subst_prec) $ go subst_prec s ++ " | " ++ prettyVar x ++ " = " ++ go sum_prec t
  go prec (SFunctorial t) = "⋄" ++ parens (prec > app_prec) (go app_prec t)
  go _        sprim@SPrim = prim sprim
    -- I can't seem to pattern match on the type here, so we have an auxiliary
    -- function instead
  
  prim :: forall a. Typeable a => Sing (Prim a) -> String
  prim _ = "⌈" ++ show (typeRep (Proxy :: Proxy a)) ++ "⌉"

  parens True  = ("(" ++) . (++ ")")
  parens False = id

freeIn :: forall (x :: Nat) (t :: FMType' Nat). Sing x -> Sing t -> Bool
x `freeIn` SVar y         = x `compareSNat` y
_ `freeIn` SZero          = False
_ `freeIn` SOne           = False
x `freeIn` (s `SPlus`  t) = (x `freeIn` s) || (x `freeIn` t)
x `freeIn` (s `STimes` t) = (x `freeIn` s) || (x `freeIn` t)
x `freeIn` SSubst s y t   = (x `freeIn` s) || (not (x `compareSNat` y) && (x `freeIn` t))
x `freeIn` SMu y t        = not (x `compareSNat` y) && (x `freeIn` t)
x `freeIn` SFunctorial t  = x `freeIn` t
_ `freeIn` SPrim          = False

type family TypeableFM (t :: FMType' id) :: Constraint where
  TypeableFM (Var x)        = ()
  TypeableFM Zero           = ()
  TypeableFM One            = ()
  TypeableFM (s :+: t)      = (TypeableFM s, TypeableFM t)
  TypeableFM (s :×: t)      = (TypeableFM s, TypeableFM t)
  TypeableFM (Mu x t)       = TypeableFM t
  TypeableFM (Subst s x t)  = (TypeableFM s, TypeableFM t)
  TypeableFM (Functorial t) = TypeableFM t
  TypeableFM (Prim t)       = Typeable t
