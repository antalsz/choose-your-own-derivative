{-# LANGUAGE LambdaCase, ScopedTypeVariables #-}

module Async where

import Control.Concurrent
import Control.Exception.Base ( AsyncException( ThreadKilled ) )

data Async a = Async { asyncThreadId :: ThreadId 
                     , _asyncWait    :: IO a }

type ZipperAsync a = (ThreadId, a)

chooseAsyncTuple :: (Async a, Async b) -> IO (Either (ZipperAsync a,Async b) (Async a,ZipperAsync b))
chooseAsyncTuple = undefined

chooseAsyncList :: [Async a] -> IO ([Async a],ZipperAsync a,[Async a])
chooseAsyncList = undefined

-- Spawning

async :: IO a -> IO (Async a)
async eA = do
  v <- newEmptyMVar
  i <- forkIO $ eA >>= putMVar v
  pure $ Async { asyncThreadId = i, _asyncWait = takeMVar v }

--Spawning with auto cancellation

withAsync :: IO a -> (Async a -> IO b) -> IO b
withAsync eA k = do
  a <- async eA
  b <- k a
  cancel a
  return b

-- Querying Asyncs (no polling behavior)

wait :: Async a -> IO a
wait a = _asyncWait a

cancel :: Async a -> IO ()
cancel a = throwTo (asyncThreadId a) ThreadKilled

-- Waiting for multiple Asyncs

waitAny :: [Async a] -> IO (Async a, a)
waitAny ls = do
  (_, (threadId, a), _) <- chooseAsyncList ls
  pure (Async threadId (pure a), a)

waitAnyCancel :: [Async a] -> IO (Async a, a)
waitAnyCancel ls = do
  (before, (threadId, a), after) <- chooseAsyncList ls
  _ <- mapM cancel (before ++ after)
  pure (Async threadId (pure a), a)

waitEither :: Async a -> Async b -> IO (Either a b)
waitEither eA eB =
  chooseAsyncTuple (eA, eB) >>= \case
    Left  ((_,a),_) -> pure $ Left a
    Right (_,(_,b)) -> pure $ Right b

waitEitherCancel :: Async a -> Async b -> IO (Either a b)
waitEitherCancel eA eB =
  chooseAsyncTuple (eA,eB) >>= \case
    Left ((_,a),eB)  -> do cancel eB
                           pure $ Left a
    Right (eA,(_,b)) -> do cancel eA
                           pure $ Right b


waitBoth :: Async a -> Async b -> IO (a,b)
waitBoth eA eB =
  chooseAsyncTuple (eA,eB) >>= \case
    Left ((_,a),eB) ->  do b <- wait eB
                           pure (a,b)
    Right (eA,(_,b)) -> do a <- wait eA
                           pure (a,b)

