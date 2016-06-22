{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, RankNTypes, ConstraintKinds, GADTs,
             DataKinds, PolyKinds, PartialTypeSignatures, TypeApplications, RecursiveDo,
             InstanceSigs, TypeInType, FlexibleContexts #-}
{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE AllowAmbiguousTypes #-}


module Choose where

import Derivatives
import SType
import Value
import Locations

import Control.Concurrent
import Data.Traversable

import Control.Applicative
import Data.Foldable


--------------------------------------------------------------------------------
-- Choosable Type Class --------------------------------------------------------
--------------------------------------------------------------------------------

class Functor f => Choosable f where
  choose :: forall a. Infer a =>
            Value f '[] a
         -> f (Value f '[] (D' 'WrtFunctor' a))


--------------------------------------------------------------------------------
-- IO Instance -----------------------------------------------------------------
--------------------------------------------------------------------------------

instance Choosable IO where
  choose = chooseIO
  
chooseIO :: forall t. Infer t => Value IO '[] t -> IO (Value IO '[] (D' 'WrtFunctor' t))
chooseIO v = do
    win <- newEmptyMVar
    v'  <- spawnallIO v
    rec threads <- forM (locations infer v') $
                   \result -> forkIO $ do
                      putMVar win =<< result
                      forM_ threads killThread
    readMVar win

spawnallIO :: Value IO '[] t -> IO (Value IO '[] t)
spawnallIO (Impure v) = do
    result <- newEmptyMVar
    _      <- forkIO $ v >>= putMVar result
    pure (Impure $ readMVar result)
spawnallIO (Inl v)     = Inl <$> spawnallIO v
spawnallIO (Inr v)     = Inr <$> spawnallIO v
spawnallIO (v1 :&: v2) = liftA2 (:&:) (spawnallIO v1) (spawnallIO v2)
spawnallIO (Wrap v)    = Wrap <$> spawnallIO v
spawnallIO v           = pure v
