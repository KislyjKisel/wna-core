{-# OPTIONS --without-K --safe #-}

module Wna.Class.Equality where

open import Wna.Prelude
open import Data.Bool.Base using (Bool; not)

module EqualityᵇFT {ℓ} (A : Set ℓ) where
    _≡ᵇ_ : Set ℓ
    _≡ᵇ_ = A → A → Bool
    _≢ᵇ_ : Set ℓ
    _≢ᵇ_ = _≡ᵇ_

record Equalityᵇ {ℓ} (A : Set ℓ) : Set ℓ where
    module FT = EqualityᵇFT A
    field
        _≡ᵇ_ : A → A → Bool
        _≢ᵇ_ : A → A → Bool

module MkEqualityᵇ {ℓ} (A : Set ℓ) where
    module FT = EqualityᵇFT A
    
    _≡ᵇ_⇒_≢ᵇ_ : FT._≡ᵇ_ → FT._≢ᵇ_
    _≡ᵇ_⇒_≢ᵇ_ _≡ᵇ_ x y = not (x ≡ᵇ y) 

    from:_≡ᵇ_ : FT._≡ᵇ_ → Equalityᵇ A
    from:_≡ᵇ_ _≡ᵇ_ = record { _≡ᵇ_ = _≡ᵇ_; _≢ᵇ_ = _≡ᵇ_⇒_≢ᵇ_ _≡ᵇ_ }

open Equalityᵇ ⦃...⦄ public
