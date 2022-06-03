{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Control.Concurrent where

open import Data.Unit.          using (⊤)
open import IO.Primitive  as IO using (IO)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Concurrent #-}

postulate
    ThreadId : Type

    forkIO : IO ⊤ → IO ThreadId

{-# COMPILE GHC ThreadId = type Control.Concurrent.ThreadId #-}

{-# COMPILE GHC forkIO = Control.Concurrent.forkIO #-}
