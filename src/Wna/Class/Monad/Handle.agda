{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Handle where

open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record Handle {ℓ} (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ monad ⦄ : RawMonad M
        
        E      : Type ℓ
        handle : ∀{A} → M A → (E → M A) → M A 

open Handle ⦃...⦄ public
    using (handle)
