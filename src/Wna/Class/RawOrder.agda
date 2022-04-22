{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawOrder where

open import Data.Bool.Base  using (Bool; not)
open import Function.Base   using (flip)
open import Wna.Primitive

record RawOrderStrict {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Type (aℓ ℓ⊔ bℓ) where
    infix 4 _<ᵇ_ _>ᵇ_ _≱ᵇ_ _≰ᵇ_
    field
        _<ᵇ_ : A → B → Bool
    
    _>ᵇ_ = flip _<ᵇ_
    _≱ᵇ_ = _<ᵇ_
    _≰ᵇ_ = _>ᵇ_

open RawOrderStrict ⦃...⦄ public

record RawOrderNonstrict {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Type (aℓ ℓ⊔ bℓ) where
    infix 4 _≤ᵇ_ _≥ᵇ_ _≯ᵇ_ _≮ᵇ_
    field
        _≤ᵇ_ : A → B → Bool
    
    _≥ᵇ_ = flip _≤ᵇ_
    _≯ᵇ_ = _≤ᵇ_
    _≮ᵇ_ = _≥ᵇ_

open RawOrderNonstrict ⦃...⦄ public
