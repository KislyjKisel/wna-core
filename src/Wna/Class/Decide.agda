{-# OPTIONS --without-K --safe #-}

module Wna.Class.Decide where

open import Function.Identity.Effectful using (Identity)

open import Relation.Nullary.Decidable public
    using (Dec; yes; no)

record DecideM {pℓ} (M : Set pℓ → Set pℓ) (P : Set pℓ) : Set pℓ where
    field
        decideM : M (Dec P)

decideM : ∀{pℓ} {M : Set pℓ → Set pℓ} (P : Set pℓ) → ⦃ DecideM M P ⦄ → M (Dec P)
decideM _ ⦃ inst ⦄ = DecideM.decideM inst

Decide : ∀{pℓ} → Set pℓ → Set pℓ
Decide = DecideM Identity

decide : ∀{pℓ} (P : Set pℓ) → ⦃ Decide P ⦄ → Dec P
decide = decideM
