{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Raise where

open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawFunctor.LevelPolymorphic   using (Fun′)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Class.RawMonad.LevelPolymorphic     using (RawMonad′)
open import Wna.Primitive

record Raise {ℓ} (M : Fun ℓ) ⦃ M-monad : RawMonad M ⦄ : Type (ℓ↑ ℓ) where
    field
        E     : Type ℓ
        raise : E → ∀{A} → M A 

open Raise ⦃...⦄ public
    using (raise)

record Raise′ (M : Fun′) ⦃ M-monad : RawMonad′ M ⦄ : Typeω where
    field
        {eℓ}   : Level
        E      : Type eℓ
        raise′ : E → ∀{aℓ} {A : Type aℓ} → M A

open Raise′ ⦃...⦄ public
    using (raise′)
