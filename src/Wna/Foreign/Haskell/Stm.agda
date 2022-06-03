{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Stm where

open import Data.Bool.Base using (Bool)
open import Data.Unit      using (⊤)
open import IO.Primitive   using (IO)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Concurrent.STM #-}

postulate
    STM : ∀{ℓ} → Type ℓ → Type ℓ

    atomically : ∀{aℓ} {A : Type aℓ} → STM A → IO A
    retry : ∀{aℓ} {A : Type aℓ} → STM A
    orElse : ∀{aℓ} {A : Type aℓ} → STM A → STM A → STM A
    check : Bool → STM ⊤
    -- throwSTM requires Exceptions
    -- catchSTM same

    -- todo: functor/applicative/monad instances for STM 

{-# FOREIGN GHC AgdaSTM ℓ = type Control.Concurrent.STM.STM #-}
{-# COMPILE GHC STM = type AgdaSTM #-}

{-# COMPILE GHC atomically = \ aℓ a → Control.Concurrent.STM.atomically #-}
{-# COMPILE GHC retry      = \ aℓ a → Control.Concurrent.STM.retry      #-}
{-# COMPILE GHC orElse     = \ aℓ a → Control.Concurrent.STM.orElse     #-}
{-# COMPILE GHC check      = \ ℓ    → Control.Concurrent.STM.check      #-}
