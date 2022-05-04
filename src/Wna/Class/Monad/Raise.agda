{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Raise where

open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record Raise {ℓ} (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ monad ⦄ : RawMonad M
        
        E     : Type ℓ
        raise : E → ∀{A} → M A 

open Raise ⦃...⦄ public
    using (raise)
