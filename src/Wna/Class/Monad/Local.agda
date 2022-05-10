{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Local where

open import Data.Unit            using (⊤)
open import Wna.Class.Monad.Ask  using (MonadAsk)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record MonadLocal {ℓ} (E : Type ℓ) (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M
        overlap ⦃ M-ask ⦄    : MonadAsk E M
    
    field
        local : (E → E) → {A : Type ℓ} → M A → M A

open MonadLocal ⦃...⦄ public
    using (local)
