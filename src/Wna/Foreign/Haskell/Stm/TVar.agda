{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Stm.TVar where

open import Data.Bool.Base          using (Bool)
open import Data.Unit               using (⊤)
open import Foreign.Haskell.Pair    using (Pair)
open import IO.Primitive            using (IO)
open import Wna.Foreign.Haskell.Base.Data.Int.Base using (Int)
open import Wna.Foreign.Haskell.Stm using (STM)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Concurrent.STM.TVar #-}

postulate
    TVar : ∀{ℓ} → Type ℓ → Type ℓ

    newTVar       : ∀{ℓ} {A   : Type ℓ} → A → STM (TVar A) 
    newTVarIO     : ∀{ℓ} {A   : Type ℓ} → A → IO (TVar A) 
    readTVar      : ∀{ℓ} {A   : Type ℓ} → TVar A → STM A 
    readTVarIO    : ∀{ℓ} {A   : Type ℓ} → TVar A → IO A
    writeTVar     : ∀{ℓ} {A   : Type ℓ} → TVar A → A → STM ⊤ 
    modifyTVar    : ∀{ℓ} {A   : Type ℓ} → TVar A → (A → A) → STM ⊤ 
    modifyTVar'   : ∀{ℓ} {A   : Type ℓ} → TVar A → (A → A) → STM ⊤
    stateTVar     : ∀{ℓ} {S A : Type ℓ} → TVar S → (S → Pair A S) → STM A
    swapTVar      : ∀{ℓ} {A   : Type ℓ} → TVar A → A → STM A
    registerDelay : ∀{ℓ} {A   : Type ℓ} → Int → IO (TVar Bool)
    
    -- mkWeakTVar : ∀{ℓ} {A : Type ℓ} → TVar A → IO ⊤ → IO (Weak (TVar A))

{-# FOREIGN GHC AgdaTVar ℓ = type Control.Concurrent.STM.TVar.TVar #-}
{-# COMPILE GHC TVar = type AgdaTVar #-}

{-# COMPILE GHC newTVar       = \ ℓ a   -> Control.Concurrent.STM.TVar.newTVar       #-}
{-# COMPILE GHC newTVarIO     = \ ℓ a   -> Control.Concurrent.STM.TVar.newTVarIO     #-}
{-# COMPILE GHC readTVar      = \ ℓ a   -> Control.Concurrent.STM.TVar.readTVar      #-}
{-# COMPILE GHC readTVarIO    = \ ℓ a   -> Control.Concurrent.STM.TVar.readTVarIO    #-}
{-# COMPILE GHC writeTVar     = \ ℓ a   -> Control.Concurrent.STM.TVar.writeTVar     #-}
{-# COMPILE GHC modifyTVar    = \ ℓ a   -> Control.Concurrent.STM.TVar.modifyTVar    #-}
{-# COMPILE GHC modifyTVar'   = \ ℓ a   -> Control.Concurrent.STM.TVar.modifyTVar'   #-}
{-# COMPILE GHC stateTVar     = \ ℓ s a -> Control.Concurrent.STM.TVar.stateTVar     #-}
{-# COMPILE GHC swapTVar      = \ ℓ a   -> Control.Concurrent.STM.TVar.swapTVar      #-}
{-# COMPILE GHC registerDelay = \ ℓ a   -> Control.Concurrent.STM.TVar.registerDelay #-}
