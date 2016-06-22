{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, RankNTypes, ConstraintKinds, GADTs,
             DataKinds, PolyKinds #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Constraints where

import Derivatives

import GHC.TypeLits
import Data.Type.Equality
import Unsafe.Coerce
import GHC.Exts
import Data.Proxy

data Dict (c :: Constraint) :: * where Dict :: c => Dict c

withDict :: Dict c -> (c => r) -> r
withDict Dict r = r

ifEqNat :: forall (x :: Nat) (y :: Nat) (r :: *).
           (KnownNat x, KnownNat y)
        => (((x == y) ~ 'True, x ~ y) => r)
        -> (((x == y) ~ 'False, (y==x) ~ 'False) => r)
        -> r
ifEqNat t f | natVal (Proxy :: Proxy x) == natVal (Proxy :: Proxy y) = isTrue t
            | otherwise = isFalse f
  where isTrue :: (((x == y) ~ 'True, x ~ y) => r) -> r
        isTrue = withDict ((unsafeCoerce :: Dict () -> Dict ((x == y) ~ 'True, x ~ y)) Dict)

        isFalse :: (((x == y) ~ 'False, (y==x) ~ 'False) => r) -> r
        isFalse = withDict ((unsafeCoerce :: Dict () -> Dict (((x == y) ~ 'False), (y == x) ~ 'False)) Dict)


-- TODO: move to wherever lookup is defined
lookupTail :: forall x y env v def. (x == y) ~ 'False
           => Lookup ('(x,v)':env) def y
           -> Lookup env def y
lookupTail l = l


lookupConsNeq :: forall x value y assocs def. (y == x) ~ 'False
              => Dict ((Lookup ('(y,value) ': assocs) def x) ~ Lookup assocs def x)
lookupConsNeq = Dict

-- TODO
lookupAppend :: forall env y value env' def x. (y == x) ~ 'False
             => Dict ((Lookup (Append env ('(y,value) ': env')) def x)
                     ~(Lookup (Append env env') def x))
lookupAppend = undefined

