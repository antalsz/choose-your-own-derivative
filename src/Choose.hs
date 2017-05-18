{-# LANGUAGE DeriveGeneric, LambdaCase,
             TypeOperators, TypeFamilies, FlexibleInstances, UndecidableInstances,
             EmptyCase, ScopedTypeVariables, RankNTypes, ConstraintKinds, GADTs,
             DataKinds, PolyKinds, PartialTypeSignatures, TypeApplications, RecursiveDo,
             InstanceSigs, TypeInType, FlexibleContexts, AllowAmbiguousTypes,
             MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wall -Wcompat -fno-warn-unticked-promoted-constructors #-}

module Choose where

import Constraints
import Types
import Derivatives
import Locations
import ToFM

import Control.Concurrent
import Control.Concurrent.Async()
import Data.Traversable
import Data.Void

--import Control.Applicative
import Data.Bitraversable
import Data.Foldable
import Data.Singletons

--------------------------------------------------------------------------------
-- Choosable Type Class --------------------------------------------------------
--------------------------------------------------------------------------------

class Functor f => Choosable f where
  choose' :: Sing t -> Interp f EmptyT t
         -> f (Interp f EmptyT (D' 'WrtFunctor t))

instance Choosable IO where
   choose' = chooseIO


choose :: forall β f α. (Choosable f, KnownD f α β) => α -> f β
choose a = fromD @f @α @β <$> choose' t (toFM @f @α a)
  where
    t :: Sing (ToFM (Just f) α)
    t = sing

-----------------
-- IO instance --
-----------------

chooseIO :: forall t. Sing t
         -> Value IO t -> IO (Value IO (D' 'WrtFunctor t))
chooseIO t v = do
    win     <- newEmptyMVar
    v'      <- spawnallIO t v
    -- locations' might be empty
    let locs = locations' @IO t v'
    if null locs 
    then error "choose called on value with no events"
    else do
      -- for every "location", fork a thread that tries write to "win"
      threads <- forM locs $ \e -> forkIO $ do x <- e
                                               putMVar win x
      victory <- readMVar win  -- the actual winner is the first event to occur
      forM_ threads killThread -- kill all other threads
      return victory


-- spawnallIO t v
-- looks for all IO actions inside v and spawns a thread for each one
-- this ensures that "waiting" for an IO event more than once doesn't
-- run that IO event more than once 
--
-- e.g. let x = print "Hi"
--      in x >> x
-- vs   do m <- newEmptyMVar
--         x <- forkIO $ print "hi" >>= putMVar m
--         readMVar m >> readMVar m
spawnallIO :: forall t. Sing t -> Value IO t -> IO (Value IO t)
spawnallIO = spawnallIO' @EmptyT


-- TODO: write documentation for this function
spawnallIO' :: forall ctx t. Sing t -> Interp IO ctx t -> IO (Interp IO ctx t)
spawnallIO' (SVar _)       i  = pure i
spawnallIO' SZero          i  = absurd i
spawnallIO' SOne           () = pure ()
spawnallIO' (SPlus  t₁ t₂) i  = bitraverse (spawnallIO' @ctx t₁) (spawnallIO' @ctx t₂) i
spawnallIO' (STimes t₁ t₂) i  = bitraverse (spawnallIO' @ctx t₁) (spawnallIO' @ctx t₂) i
spawnallIO' (SMu (_ :: Sing x) (t' :: Sing t')) (Con i) =
  Con <$> spawnallIO' @(AddT ctx x ('Mu x t')) t' i
spawnallIO' (SSubst t (_ :: Sing x) (_ :: Sing s)) i = spawnallIO' @(AddT ctx x s) t i
spawnallIO' (SFunctorial _) i = do
  result <- newEmptyMVar
  _      <- forkIO $ i >>= putMVar result
  pure $ readMVar result
spawnallIO' SPrim i = pure i

