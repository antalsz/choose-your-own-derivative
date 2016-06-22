{-# LANGUAGE CPP, DataKinds #-}

module Compat where

import GHC.Generics

-- GHC 8 compatibility
#if __GLASGOW_HASKELL__ >= 761
type NoSelector = 'MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy
#endif
