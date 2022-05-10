{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Free.Church.Base where

open import Data.Container.Core using (Container; ⟦_⟧)
open import Wna.Primitive

record FreeT {ℓ} (F M : Container ℓ ℓ) (A : Type ℓ) : Type ℓ where
    constructor mkFree
    field
        runFree : ∀{R : Type ℓ} → (A → ⟦ M ⟧ R) → (∀{X : Type ℓ} → (X → ⟦ M ⟧ R) → ⟦ F ⟧ X → ⟦ M ⟧ R) → ⟦ M ⟧ R

error: ℓ↑ ℓ > ℓ
impredicativity?
