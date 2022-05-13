{-# OPTIONS --without-K --safe #-}

module Wna.Data.Scientific.Unnormalized.Base where

open import Data.Integer.Base as ℤ using (ℤ)
open import Data.Nat.Base     as ℕ using (ℕ)
open import Wna.Primitive

record Scientificᵘ {base : ℕ} (base≥2 : base ℕ.≥ 2) : Type where
    no-eta-equality
    pattern
    constructor mkScientificᵘ
    field
        coefficient exponent : ℤ

open Scientificᵘ public
    using (coefficient; exponent)

-_ : ∀{base} {base≥2 : base ℕ.≥ 2} → Scientificᵘ base≥2 → Scientificᵘ base≥2
-_ (mkScientificᵘ c e) = mkScientificᵘ (ℤ.- c) e 

-- todo: arithmetic

-- todo: data Isℤ : Scientific → Type where
 