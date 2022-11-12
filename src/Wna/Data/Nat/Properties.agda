{-# OPTIONS --without-K --safe #-}

module Wna.Data.Nat.Properties where

open import Data.Nat.Divisibility
open import Data.Product                               using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_)
open import Wna.Data.Nat.Base

open import Data.Nat.Properties public

-- log

log-rem≢0 : ∀ m ⦃ _ : NonZero m ⦄ {d} {d≥2 : d ≥ 2} → proj₁ (proj₂ (log m d≥2)) ≢ 0
log-rem≢0 m ⦃ mnz ⦄ {d} {d≥2} r≡0 with log m d≥2
... | (e , r , p) = p (≡.subst (d ∣_) (≡.sym r≡0) (d ∣0))
