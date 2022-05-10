{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Free where

open import Wna.Class.RawMonad using (RawMonad)
open import Wna.Primitive

record MonadFree {ℓ} (F M : Type ℓ → Type ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M

        wrap : ∀{A} → F (M A) → M A

module Instanced where
    open MonadFree ⦃...⦄ public