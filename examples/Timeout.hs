{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}

module Timeout where

import Control.Concurrent
import GHC.Event

import Async


timeoutEvent :: Int -> IO ()
timeoutEvent n = do
  timer <- getSystemTimerManager
  v <- newEmptyMVar
  _ <- registerTimeout timer n $ putMVar v ()
  takeMVar v

timeout :: Int -> IO a -> IO (Maybe a)
timeout n eA = do
  tA <- async $ timeoutEvent n
  eA <- async eA
  waitEitherCancel tA eA >>= \case
    -- the timeout triggered first
    Left () -> return Nothing
    
    -- the event triggered first
    Right a -> return $ Just a

