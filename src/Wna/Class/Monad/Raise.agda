{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Raise where

open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record MonadRaise {ℓ} (E : Type ℓ) (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M
        
        raise : E → ∀{A} → M A 

module Instanced where
    open MonadRaise ⦃...⦄ public
        using (raise)
