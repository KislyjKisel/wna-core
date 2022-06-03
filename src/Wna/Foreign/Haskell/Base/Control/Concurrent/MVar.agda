{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Control.Concurrent.MVar where

open import Data.Bool.Base              using (Bool)
open import Data.Maybe.Base             using (Maybe)
open import Data.Unit                   using (⊤)
open import Foreign.Haskell.Pair        using (Pair)
open import IO.Primitive          as IO using (IO)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Concurrent.MVar #-}

postulate
    MVar : ∀{ℓ} → Type ℓ → Type ℓ

    newEmptyMVar     : ∀{aℓ   } {A : Type aℓ}               → IO (MVar A)
    newMVar          : ∀{aℓ   } {A : Type aℓ}               → A → IO (MVar A)
    takeMVar         : ∀{aℓ   } {A : Type aℓ}               → MVar A → IO A
    putMVar          : ∀{aℓ   } {A : Type aℓ}               → MVar A → A → IO ⊤
    readMVar         : ∀{aℓ   } {A : Type aℓ}               → MVar A → IO A
    swapMVar         : ∀{aℓ   } {A : Type aℓ}               → MVar A → A → IO A
    tryTakeMVar      : ∀{aℓ   } {A : Type aℓ}               → MVar A → IO (Maybe A)
    tryPutMVar       : ∀{aℓ   } {A : Type aℓ}               → MVar A → A → IO Bool
    isEmptyMVar      : ∀{aℓ   } {A : Type aℓ}               → MVar A → IO Bool
    withMVar         : ∀{aℓ bℓ} {A : Type aℓ} {B : Type bℓ} → MVar A → (A → IO B) → IO B
    withMVarMasked   : ∀{aℓ bℓ} {A : Type aℓ} {B : Type bℓ} → MVar A → (A → IO B) → IO B 
    modifyMVar       : ∀{aℓ bℓ} {A : Type aℓ} {B : Type bℓ} → MVar A → (A → IO (Pair A B)) → IO B
    modifyMVarMasked : ∀{aℓ bℓ} {A : Type aℓ} {B : Type bℓ} → MVar A → (A → IO (Pair A B)) → IO B
    tryReadMVar      : ∀{aℓ   } {A : Type aℓ}               → MVar A → IO (Maybe A)
    mkWeakMVar       : ∀{aℓ   } {A : Type aℓ}               → MVar A → IO (Maybe A)


{-# FOREIGN GHC AgdaMVar ℓ = type Control.Concurrent.MVar.MVar #-}
{-# COMPILE GHC MVar = type AgdaMVar #-}

{-# COMPILE GHC newEmptyMVar     = \ aℓ a      → Control.Concurrent.MVar.newEmptyMVar     #-}
{-# COMPILE GHC newMVar          = \ aℓ a      → Control.Concurrent.MVar.newMVar          #-}
{-# COMPILE GHC takeMVar         = \ aℓ a      → Control.Concurrent.MVar.takeMVar         #-}
{-# COMPILE GHC putMVar          = \ aℓ a      → Control.Concurrent.MVar.putMVar          #-}
{-# COMPILE GHC readMVar         = \ aℓ a      → Control.Concurrent.MVar.readMVar         #-}
{-# COMPILE GHC swapMVar         = \ aℓ a      → Control.Concurrent.MVar.swapMVar         #-}
{-# COMPILE GHC tryTakeMVar      = \ aℓ a      → Control.Concurrent.MVar.tryTakeMVar      #-}
{-# COMPILE GHC tryPutMVar       = \ aℓ a      → Control.Concurrent.MVar.tryPutMVar       #-}
{-# COMPILE GHC isEmptyMVar      = \ aℓ a      → Control.Concurrent.MVar.isEmptyMVar      #-}
{-# COMPILE GHC withMVar         = \ aℓ bℓ a b → Control.Concurrent.MVar.withMVar         #-}
{-# COMPILE GHC withMVarMasked   = \ aℓ bℓ a b → Control.Concurrent.MVar.withMVarMasked   #-}
{-# COMPILE GHC modifyMVar       = \ aℓ bℓ a b → Control.Concurrent.MVar.modifyMVar       #-}
{-# COMPILE GHC modifyMVarMasked = \ aℓ bℓ a b → Control.Concurrent.MVar.modifyMVarMasked #-}
{-# COMPILE GHC tryReadMVar      = \ aℓ a      → Control.Concurrent.MVar.tryReadMVar      #-}
{-# COMPILE GHC mkWeakMVar       = \ aℓ a      → Control.Concurrent.MVar.mkWeakMVar       #-}
    