{-# OPTIONS --without-K --safe #-}

module Wna.Algebra.Field.Rational where

open import Data.Product using (_,_)
open import Data.Rational
open import Data.Rational.Properties
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality.Properties using () renaming (isEquivalence to ≡-equiv)
open import Wna.Algebra.Field

ℚ-rawField : RawField 0ℓ 0ℓ
ℚ-rawField = record
    { Carrier = ℚ
    ; _≈_ = _≡_
    ; _+_ = _+_
    ; _*_ = _*_
    ; -_ = -_
    ; _⁻¹ = λ {x} x≢0 → 1/_ x ⦃ ≢-nonZero x≢0 ⦄
    ; 0# = 0ℚ
    ; 1# = 1ℚ
    }

ℚ-isField : IsField ℚ-rawField
ℚ-isField = record
    { ≈-equiv     = ≡-equiv
    ; +-assoc     = +-assoc
    ; *-assoc     = *-assoc
    ; +-comm      = +-comm
    ; *-comm      = *-comm
    ; *-distrib-+ = *-distrib-+
    ; +-identity  = +-identity
    ; *-identity  = *-identity
    ; +-inverse   = +-inverse
    ; *-inverse   = (λ {x} x≢0 → *-inverseˡ x ⦃ ≢-nonZero x≢0 ⦄) , λ {x} x≢0 → *-inverseʳ x ⦃ ≢-nonZero x≢0 ⦄
    ; 0≉1         = λ ()
    }

ℚ-field : Field 0ℓ 0ℓ
ℚ-field = record
    { rawField = ℚ-rawField
    ; isField  = ℚ-isField
    }