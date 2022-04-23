{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawEquality where

open import Data.Bool.Base using (Bool; not)
open import Wna.Primitive

module RawEqualityFT {aℓ} {bℓ} (A : Type aℓ) (B : Type bℓ) where
    _≡ᵇ_ : Type (aℓ ℓ⊔ bℓ)
    _≡ᵇ_ = A → B → Bool
    _≢ᵇ_ : Type (aℓ ℓ⊔ bℓ)
    _≢ᵇ_ = _≡ᵇ_

record RawEquality {aℓ} {bℓ} (A : Type aℓ) (B : Type bℓ) : Type (aℓ ℓ⊔ bℓ) where
    private module FT = RawEqualityFT A B
    infix 4 _≡ᵇ_ _≢ᵇ_
    field
        _≡ᵇ_ : A → B → Bool
        _≢ᵇ_ : A → B → Bool

open RawEquality ⦃...⦄ public

module MkRawEquality {aℓ} {bℓ} (A : Type aℓ) (B : Type bℓ) where
    private
        module FT = RawEqualityFT A B
    
    _≡ᵇ_⇒_≢ᵇ_ : FT._≡ᵇ_ → FT._≢ᵇ_
    _≡ᵇ_⇒_≢ᵇ_ _≡ᵇ_ x y = not (x ≡ᵇ y) 

    from:_≡ᵇ_ : FT._≡ᵇ_ → RawEquality A B
    from:_≡ᵇ_ _≡ᵇ_ = record { _≡ᵇ_ = _≡ᵇ_; _≢ᵇ_ = _≡ᵇ_⇒_≢ᵇ_ _≡ᵇ_ }
