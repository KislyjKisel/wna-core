{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Handle where

open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawFunctor.LevelPolymorphic   using (Fun′)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Class.RawMonad.LevelPolymorphic     using (RawMonad′)
open import Wna.Primitive

record Handle {ℓ} (M : Fun ℓ) ⦃ M-monad : RawMonad M ⦄ : Type (ℓ↑ ℓ) where
    field
        E      : Type ℓ
        handle : ∀{A} → M A → (E → M A) → M A 

open Handle ⦃...⦄ public
    using (handle)

record Handle′ (M : Fun′) ⦃ M-monad : RawMonad′ M ⦄ : Typeω where
    field
        {eℓ}    : Level
        E       : Type eℓ
        handle′ : ∀{aℓ} {A : Type aℓ} → M A → (E → M A) → M A

open Handle′ ⦃...⦄ public
    using (handle′)
