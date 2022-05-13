{-# OPTIONS --without-K --safe #-}

module Wna.Data.Scientific.Base where

open import Data.Integer                          as ℤ  using (ℤ)
open import Data.Integer.Properties               as ℤ  using ()
open import Data.Nat                              as ℕ  using (ℕ; nonZero)
open import Data.Nat.Divisibility                 as ℕ  using ()
open import Data.Nat.Induction                    as ℕ  using ()
open import Data.Nat.Properties                   as ℕ  using ()
open import Function.Base                               using (it; _$_)
open import Induction.WellFounded                       using (Acc)
open import Relation.Binary.Definitions                 using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality as ≡  using (_≡_; _≢_)
open import Relation.Nullary                            using (yes; no)
open import Relation.Nullary.Negation                   using (contradiction)
open import Wna.Primitive

record Scientific {base : ℕ} (base≥2 : base ℕ.≥ 2) : Type where
    no-eta-equality
    pattern
    constructor mkScientific
    field
        coefficient exponent : ℤ
        normalized : ⦃ _ : ℤ.NonZero coefficient ⦄ → base ℕ.∤ ℤ.∣ coefficient ∣

-_ : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientific base≥2 → Scientific base≥2
-_ {base} (mkScientific c e p) = mkScientific (ℤ.- c) e (≡.subst (base ℕ.∤_) (≡.sym $ ℤ.∣-i∣≡∣i∣ c) $ p ⦃ ≡.subst ℕ.NonZero (ℤ.∣-i∣≡∣i∣ c) it ⦄) 

private
    normalizePositive : ∀{base} {base≥2 : base ℕ.≥ 2} (c : ℕ) → c ≢ 0 → ℤ → Acc ℕ._<_ c → Scientific base≥2
    normalizePositive {b} {b≥2} c c≢0 e (ℕ.acc rs) with b ℕ.∣? c
    ... | yes p = normalizePositive (ℕ.quotient p) quotient≢0 ((ℤ.+ 1) ℤ.+ e) $ rs _ $ lemma
        where
        quotient≢0 : ℕ.quotient p ≢ 0
        quotient≢0 q≡0 = c≢0 $ ≡.trans (ℕ._∣_.equality p) (≡.subst (λ t → t ℕ.* b ≡ 0) (≡.sym q≡0) ≡.refl)    
        instance
            quotient-nonZero : ℕ.NonZero (ℕ.quotient p)
            quotient-nonZero = ℕ.≢-nonZero quotient≢0

        lemma : ℕ.quotient p ℕ.< c
        lemma = ≡.subst (_ ℕ.<_) (≡.sym $ ℕ._∣_.equality p) (ℕ.m<m*n (ℕ.quotient p) b b≥2)

    ... | no ¬p = mkScientific (ℤ.+ c) e ¬p

    lemma : ∀ i → i ≢ (ℤ.+ 0) → ℤ.∣ i ∣ ≢ 0
    lemma (ℤ.+_ n)     ≉ n≡0 = ≉ $ ≡.cong ℤ.+_ n≡0
    lemma (ℤ.negsuc n) ≉ ()

normalize : ∀{base} {base≥2 : base ℕ.≥ 2} → ℤ → ℤ → Scientific base≥2
normalize c e with ℤ.<-cmp c (ℤ.+ 0)
... | tri< < ≉ ≯ = - (normalizePositive ℤ.∣ c ∣ (lemma c ≉) e $ ℕ.<-wellFounded _)
... | tri≈ ≮ ≈ ≯ = mkScientific ℤ.0ℤ ℤ.1ℤ $ contradiction ≡.refl $ ℕ.≢-nonZero⁻¹ _
... | tri> ≮ ≉ > = normalizePositive ℤ.∣ c ∣ (lemma c ≉) e $ ℕ.<-wellFounded _
