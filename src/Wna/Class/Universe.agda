{-# OPTIONS --without-K --safe #-}

module Wna.Class.Universe where

open import Data.Nat.Base                       using (zero; suc)
open import Data.Product                        using (_,_)
open import Function.Nary.NonDependent.Base     using (Levels; ⨆)
open import Level as ℓ                          using (Level)

private
    nary : ∀ arity → (pℓs : Levels arity) → (eℓ : Level) → Set (ℓ.suc (⨆ arity pℓs ℓ.⊔ eℓ))
    nary zero pℓs eℓ = Set eℓ
    nary (suc arity) (pℓ , pℓs) eℓ = Set pℓ → nary arity pℓs eℓ

record Universe {uℓ} arity (pℓs : Levels arity) eℓ (U : Set uℓ) : Set (uℓ ℓ.⊔ ℓ.suc (⨆ arity pℓs ℓ.⊔ eℓ)) where
    constructor universe
    field
        ⟦_⟧ : U → nary arity pℓs eℓ

open Universe ⦃...⦄ public
