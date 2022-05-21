{-# OPTIONS --without-K --safe #-}

module Wna.Data.Scientific.Unnormalized.Base where

open import Data.Integer.Base        as ℤ   using (ℤ)
open import Data.Integer.Properties  as ℤ   using ()
open import Wna.Data.Nat.Base        as ℕ   using (ℕ)
open import Wna.Data.Nat.Properties  as ℕ   using ()
open import Wna.Data.Scientific.Base as Sci using (Scientific)
open import Data.Float.Base          as Flt using (Float)
open import Data.Maybe.Base          as Mb  using (Maybe)
open import Data.Product             as Σ   using (Σ; proj₁; _×_; _,_)
open import Function.Base                   using (_∘′_; _$_)
open import Relation.Nullary using (yes; no)
open import Wna.Primitive
open import Data.Nat.Divisibility as ℕ using ()
open import Relation.Binary.Definitions                using (tri<; tri≈; tri>)
open import Relation.Nullary using (yes; no)
open import Data.String.Base as Str using (String)
open import Data.List.Base as List using (List)
open import Data.Char.Base using (Char)

record Scientificᵘ {base : ℕ} (base≥2 : base ℕ.≥ 2) : Type where
    no-eta-equality
    pattern
    constructor mkScientificᵘ
    field
        significand exponent : ℤ

open Scientificᵘ public
    using (significand; exponent)

-- todo: easy specialization of type to any base using decidable `2 ≤? base`
-- todo: to, from: ℤ, ℕ, ℚ

0𝕊ᵘ : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientificᵘ base≥2
0𝕊ᵘ = mkScientificᵘ ℤ.0ℤ ℤ.0ℤ

1𝕊ᵘ : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientificᵘ base≥2
1𝕊ᵘ = mkScientificᵘ ℤ.1ℤ ℤ.0ℤ

Scientificᵘ₂ : Type
Scientificᵘ₂ = Scientificᵘ {2} $ ℕ.s≤s $ ℕ.s≤s ℕ.z≤n

Scientificᵘ₁₀ : Type
Scientificᵘ₁₀ = Scientificᵘ {10} $ ℕ.s≤s $ ℕ.s≤s ℕ.z≤n

-- private
--     aux : ∀{b₁} {b₁≥2 : b₁ ℕ.≥ 2} {b₂} → (b₂≥2 : b₂ ℕ.≥ 2) → ℕ → ℤ → Scientificᵘ b₂≥2
--     aux x = x
--         where
--         ∣x∣ : ℕ
--         ∣x∣ = ℤ.∣ x ∣
--         xlogb₂ : ℕ × ℕ
--         xlogb₂ = Σ.map₂ proj₁ $ ℕ.log ∣x∣ ⦃ {!   !} ⦄ {!   !}

-- rebase : ∀{b₁} {b₁≥2 : b₁ ℕ.≥ 2} {b₂} → (b₂≥2 : b₂ ℕ.≥ 2) → Scientificᵘ b₁≥2 → Scientificᵘ b₂≥2
-- rebase {b₁} {b₁≥2} {b₂} b₂≥2 (mkScientificᵘ x e) with ℤ.<-cmp x (ℤ.+ 0)
-- ... | tri≈ ≮ ≈ ≯ = 0𝕊ᵘ
-- ... | tri< < ≉ ≯ = {!   !}
-- ... | tri> ≮ ≉ > = {!   !}

-_ : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientificᵘ base≥2 → Scientificᵘ base≥2
-_ (mkScientificᵘ c e) = mkScientificᵘ (ℤ.- c) e 

normalize : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientificᵘ base≥2 → Scientific base≥2
normalize (mkScientificᵘ c e) = Sci.normalize c e

toFloat : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientificᵘ base≥2 → Float
toFloat {b} (mkScientificᵘ s e) = Flt.fromℤ s Flt.* Flt.fromℕ b Flt.** Flt.fromℤ e

fromFloat′ : Float → Maybe Scientificᵘ₂
fromFloat′ = Mb.map (λ (m , e) → mkScientificᵘ m e) ∘′ Flt.decode

toFloat′ : Scientificᵘ₂ → Maybe Float
toFloat′ (mkScientificᵘ m e) = Flt.encode m e

-- todo: arithmetic
-- todo: data Isℤ : Scientific → Type where
 