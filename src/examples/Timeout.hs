{-# LANGUAGE LambdaCase, ScopedTypeVariables, TypeApplications, DataKinds, TypeOperators,
             FlexibleInstances, MultiParamTypeClasses, TypeFamilies, FlexibleContexts #-}

module Timeout where

import Control.Concurrent
import GHC.Event

import Constraints
import Types
import Choose
import ToFM
import Equiv


-- threadDelay :: Int -> IO ()


timeout :: forall a. KnownFM IO a => Int -> IO a -> IO (Maybe a)
timeout n evt = do
    x <- choose (evt, threadDelay n)
    case x of 
        Left  (a,_:: IO ())    -> pure $ Just a
        Right (_ :: (IO a,())) -> pure Nothing














----------------------------------------------------


raceTimeouts :: IO ()
raceTimeouts = do
    (pre,MyString str1,post) <- choose @([IO MyString],MyString,[IO MyString])
                                  [ threadDelay 1 >> return (MyString "Hello")
                                  , threadDelay 1 >> return (MyString "PL")
                                  , threadDelay 1 >> return (MyString "Club") ]
    (pre,MyString str2,post) <- choose @([IO MyString],MyString,[IO MyString])
                                $ pre ++ post
    ( [], MyString str3, []) <- choose @([IO MyString],MyString,[IO MyString])
                                $ pre ++ post
    print $ str1 ++ " " ++ str2 ++ " " ++ str3


raceAll :: [IO MyString] -> IO ()
raceAll [] = return ()
raceAll ls = do (pre, MyString str, post) <- choose ls 
                print str
                raceAll $ pre ++ post


raceTimeouts' :: IO ()
raceTimeouts' = raceAll [ threadDelay 1 >> return (MyString "Hello")
                        , threadDelay 1 >> return (MyString "PL")
                        , threadDelay 1 >> return (MyString "Club") ]




newtype MyString = MyString String
type instance ToFM f MyString = Prim String
instance KnownFM f MyString where
  toFM (MyString s) = s
  fromFM = MyString
  emptyDom = WSPrim


