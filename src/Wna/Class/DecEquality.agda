{-# OPTIONS --without-K --safe #-}

module Wna.Class.DecEquality where

open import Relation.Binary.Definitions             using (Decidable)
open import Relation.Binary.PropositionalEquality   using (_≡_)
open import Wna.Primitive

record DecEquality {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infix 4 _≈_ _≈?_
    field
        { rℓ  } : _
        { _≈_ } : A → B → Type rℓ
        _≈?_    : Decidable _≈_

open DecEquality ⦃...⦄ public

record DecPropositionalEquality {aℓ} (A : Type aℓ) : Type aℓ where
    infix 4 _≡?_
    field
        _≡?_ : Decidable {A = A} _≡_

open DecPropositionalEquality ⦃...⦄ public
