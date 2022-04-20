{-# OPTIONS --without-K --safe #-}

module Wna.Algebra.Field where

import Algebra.Definitions
open import Algebra using (Op₁; Op₂)
open import Algebra.Bundles using (RawRing)
open import Data.Product using (_×_; proj₁; proj₂)
open import Level using (_⊔_) renaming (suc to lsuc)
open import Relation.Binary using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary using (¬_)

record RawField c ℓ : Set (lsuc (c ⊔ ℓ)) where
    infix  8 -_
    infixl 7 _*_
    infixl 6 _+_
    infix  4 _≈_

    field
        Carrier : Set c
        _≈_     : Rel Carrier ℓ
        _+_     : Op₂ Carrier
        _*_     : Op₂ Carrier
        -_      : Op₁ Carrier
        0#      : Carrier
        1#      : Carrier
        _⁻¹     : {x : Carrier} → ¬ (x ≈ 0#) → Carrier

    infix 4 _≉_
    _≉_ : Rel Carrier ℓ
    x ≉ y = ¬ (x ≈ y)

    infixl 6 _-_
    _-_ : Op₂ Carrier
    x - y = x + (- y)

record IsField {c ℓ} (F : RawField c ℓ) : Set (c ⊔ ℓ) where
    open RawField F
    open Algebra.Definitions _≈_

    field
        ≈-equiv     : IsEquivalence _≈_
        +-assoc     : Associative _+_
        *-assoc     : Associative _*_
        +-comm      : Commutative _+_
        *-comm      : Commutative _*_
        *-distrib-+ : _*_ DistributesOver _+_
        +-identity  : Identity 0# _+_
        *-identity  : Identity 1# _*_
        +-inverse   : Inverse 0# -_ _+_
        *-inverse   : (∀{x} → (x≉0 : x ≉ 0#) → ((x≉0 ⁻¹) * x) ≈ 1#) × (∀{x} → (x≉0 : x ≉ 0#) → (x * (x≉0 ⁻¹)) ≈ 1#)
        0≉1         : 0# ≉ 1#

    module ≈-equiv = IsEquivalence ≈-equiv

    +-identityˡ : LeftIdentity 0# _+_
    +-identityˡ = proj₁ +-identity
    
    +-identityʳ : RightIdentity 0# _+_
    +-identityʳ = proj₂ +-identity

    *-identityˡ : LeftIdentity 1# _*_
    *-identityˡ = proj₁ *-identity
    
    *-identityʳ : RightIdentity 1# _*_
    *-identityʳ = proj₂ *-identity

    *-distribˡ-+ : _*_ DistributesOverˡ _+_
    *-distribˡ-+ = proj₁ *-distrib-+

    *-distribʳ-+ : _*_ DistributesOverʳ _+_
    *-distribʳ-+ = proj₂ *-distrib-+

    +-inverseˡ : LeftInverse 0# -_ _+_
    +-inverseˡ = proj₁ +-inverse
    
    +-inverseʳ : RightInverse 0# -_ _+_
    +-inverseʳ = proj₂ +-inverse

    *-inverseˡ : ∀{x} → (x≉0 : x ≉ 0#) → ((x≉0 ⁻¹) * x) ≈ 1#
    *-inverseˡ = proj₁ *-inverse
    
    *-inverseʳ : ∀{x} → (x≉0 : x ≉ 0#) → (x * (x≉0 ⁻¹)) ≈ 1#
    *-inverseʳ = proj₂ *-inverse

record Field c ℓ : Set (lsuc (c ⊔ ℓ)) where
    field
        rawField : RawField c ℓ
        isField  : IsField rawField

    open RawField rawField public
    open IsField  isField  public