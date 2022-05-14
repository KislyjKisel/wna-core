{-# OPTIONS --without-K --safe #-}

module Wna.Data.Nat.Base where

open import Data.Nat.Divisibility
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Data.Product                          as Σ using (Σ; _,_; _×_)
open import Function.Base                              using (_$_)
open import Induction.WellFounded                      using (Acc)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_)
open import Relation.Nullary                           using (yes; no)
open import Wna.Primitive

open import Data.Nat.Base public

iterate : ℕ → ∀{ℓ} {A : Type ℓ} → (A → A) → A → A
iterate zero    f x = x
iterate (suc n) f x = iterate n f (f x)

log : (x : ℕ) ⦃ _ : NonZero x ⦄ → {d : ℕ} → d ≥ 2 → ℕ × Σ ℕ (d ∤_)
log x d≥2 = aux x d≥2 $ <-wellFounded x
    where
    aux : (x : ℕ) ⦃ _ : NonZero x ⦄ → {d : ℕ} → d ≥ 2 → Acc _<_ x → ℕ × Σ ℕ (d ∤_)
    aux x ⦃ xnz ⦄ {d} d≥2 (acc rs) with d ∣? x
    ... | no  d∤x = 0 , x , d∤x
    ... | yes d∣x  = Σ.map₁ suc $ aux (quotient d∣x) d≥2 $ rs _ recwf
        where
        q≢0 : quotient d∣x ≢ 0
        q≢0 q≡0 = ≢-nonZero⁻¹ x $ ≡.trans (_∣_.equality d∣x) $ ≡.subst (λ t → t * d ≡ 0) (≡.sym q≡0) ≡.refl
        instance
            q-nZ = ≢-nonZero q≢0

        recwf : quotient d∣x < x
        recwf = ≡.subst (quotient d∣x <_) (≡.sym $ _∣_.equality d∣x) $ m<m*n (quotient d∣x) d d≥2
