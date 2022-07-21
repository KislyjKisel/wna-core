{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Control.Concurrent where

open import Data.Unit           using (⊤)
open import IO.Primitive  as IO using (IO)
open import Wna.Foreign.Haskell.Base.Data.Int.Base using (Int)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Concurrent #-}

postulate
    ThreadId : Type

    forkIO      : IO ⊤ → IO ThreadId
    threadDelay : Int -> IO ⊤

{-# COMPILE GHC ThreadId = type Control.Concurrent.ThreadId #-}

{-# COMPILE GHC forkIO      = Control.Concurrent.forkIO      #-}
{-# COMPILE GHC threadDelay = Control.Concurrent.threadDelay #-}
