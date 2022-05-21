{-# OPTIONS --without-K --safe #-}

module Wna.Data.Scientific.Base where

open import Data.Nat.Divisibility                 as ℕ using ()
open import Data.Product                               using (Σ; proj₁; proj₂; _×_; _,_)
open import Data.Sum.Base                         as ⊎ using (inj₁; inj₂; _⊎_) 
open import Function.Base                              using (it; _$_)
open import Relation.Binary.Definitions                using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_)
open import Relation.Nullary.Negation                  using (contradiction)
open import Wna.Data.Integer.Base                 as ℤ using (ℤ)
open import Wna.Data.Integer.Properties           as ℤ using ()
open import Wna.Data.Nat.Base                     as ℕ using (ℕ)
open import Wna.Data.Nat.Properties               as ℕ using ()
open import Wna.Primitive

record Scientific {base : ℕ} (base≥2 : base ℕ.≥ 2) : Type where
    no-eta-equality
    pattern
    constructor mkScientific
    field
        significand   : ℤ
        exponent      : ℤ
        .normalized   : ⦃ _ : ℤ.NonZero significand ⦄ → base ℕ.∤ ℤ.∣ significand ∣
        .normalized-0 : significand ≢ ℤ.0ℤ ⊎ exponent ≡ ℤ.0ℤ

0𝕊 : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientific base≥2
0𝕊 = mkScientific ℤ.0ℤ ℤ.0ℤ (λ ⦃ znz ⦄ → contradiction ≡.refl $ ℕ.≢-nonZero⁻¹ _ ⦃ znz ⦄) (inj₂ ≡.refl)

1𝕊 : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientific base≥2
1𝕊 {base≥2 = b≥2} = mkScientific ℤ.1ℤ ℤ.0ℤ (λ b∣1 → ℕ.1+n≰n {1} (≡.subst (2 ℕ.≤_) (ℕ.∣1⇒≡1 b∣1) b≥2)) (inj₁ λ())

Scientific₂ : Type
Scientific₂ = Scientific {2} $ ℕ.s≤s $ ℕ.s≤s ℕ.z≤n

Scientific₁₀ : Type
Scientific₁₀ = Scientific {10} $ ℕ.s≤s $ ℕ.s≤s ℕ.z≤n

open Scientific public
    using (significand; exponent)

-_ : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientific base≥2 → Scientific base≥2
-_ {base} (mkScientific c e p1 p2) = mkScientific (ℤ.- c) e (≡.subst (base ℕ.∤_) (≡.sym $ ℤ.∣-i∣≡∣i∣ c) $ p1 ⦃ ≡.subst ℕ.NonZero (ℤ.∣-i∣≡∣i∣ c) it ⦄) (⊎.map₁ (λ c≢0 -c≡0 → c≢0 (ℤ.neg-injective -c≡0)) p2)

private
    normalizePositive' : ∀{base} {base≥2 : base ℕ.≥ 2} (c : ℕ) → ⦃ _ : ℕ.NonZero c ⦄ → ℤ → Scientific base≥2
    normalizePositive' {b} {b≥2} c e = aux c (ℕ.log c b≥2) ≡.refl
        where
        aux : (c : ℕ) → ⦃ _ : ℕ.NonZero c ⦄ → (l : ℕ × Σ ℕ (b ℕ.∤_)) → ℕ.log c b≥2 ≡ l → Scientific b≥2
        aux c (de , rx , p) s = mkScientific (ℤ.+ rx) (ℕ.iterate de ℤ.suc e) p (inj₁ $ λ rx≡0 → (≡.subst (λ t → proj₁ (proj₂ t) ≢ 0) s $ ℕ.log-rem≢0 c {b} {b≥2}) $ ℤ.+-injective rx≡0)

normalize : ∀{base} {base≥2 : base ℕ.≥ 2} → ℤ → ℤ → Scientific base≥2
normalize c e with ℤ.<-cmp c (ℤ.+ 0)
... | tri< < ≉ ≯ = - (normalizePositive' ℤ.∣ c ∣ ⦃ ℕ.≢-nonZero $ ℤ.i≢0⇒∣i∣≢0 c ≉ ⦄ e)
... | tri≈ ≮ ≈ ≯ = 0𝕊
... | tri> ≮ ≉ > = normalizePositive' ℤ.∣ c ∣ ⦃ ℕ.≢-nonZero $ ℤ.i≢0⇒∣i∣≢0 c ≉ ⦄ e
