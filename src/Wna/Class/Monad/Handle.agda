{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Handle where

open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record MonadHandle {ℓ} (E : Type ℓ) (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M
        
        handle : ∀{A} → M A → (E → M A) → M A 

module Instanced where
    open MonadHandle ⦃...⦄ public
        using (handle)
