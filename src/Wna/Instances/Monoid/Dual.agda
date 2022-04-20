{-# OPTIONS --without-K --safe #-}

module Wna.Instances.Monoid.Dual where

open import Wna.Class.Monoid using (Monoid; Dual; mkDual; getDual)

Dual-Monoid : ∀{aℓ}{A : Set aℓ} ⦃ _ : Monoid A ⦄ → Monoid (Dual A)
Dual-Monoid ⦃ M ⦄ = record { ε = mkDual ε ; _<>_ = λ x y → mkDual (getDual y <> getDual x) }
    where open Monoid M
