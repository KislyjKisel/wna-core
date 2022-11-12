{-# OPTIONS --without-K --safe #-}

module Wna.Relation.Nullary.Decidable where

open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Negation using (¬_)

open import Relation.Nullary.Decidable public

to⊎ : ∀{pℓ} {P : Set pℓ} → Dec P → (¬ P) ⊎ P
to⊎ (yes p) = inj₂ p
to⊎ (no ¬p) = inj₁ ¬p
