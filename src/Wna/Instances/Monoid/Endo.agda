{-# OPTIONS --without-K --safe #-}

module Wna.Instances.Monoid.Endo where

open import Wna.Class.Monoid using (Monoid; Endo; mkEndo)
open import Function.Base using (id; _∘′_)

Endo-Monoid : ∀{aℓ}{A : Set aℓ} → Monoid (Endo A)
Endo-Monoid = record { ε = mkEndo id ; _<>_ = λ (mkEndo f) (mkEndo g) → mkEndo (f ∘′ g) }
