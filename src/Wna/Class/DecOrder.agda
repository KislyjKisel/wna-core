{-# OPTIONS --without-K --safe #-}

module Wna.Class.DecOrder where

open import Relation.Binary.Definitions using (Decidable)
open import Function.Base               using (flip)
open import Wna.Primitive

record DecStrictOrder {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infix 4 _<_ _<?_ _>?_
    field
        { rℓ  } : _
        { _<_ } : A → B → Type rℓ
        _<?_    : Decidable _<_

    _>?_ = flip _<?_

open DecStrictOrder ⦃...⦄ public

record DecOrder {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infix 4 _≤_ _≤?_ _≥?_
    field
        { rℓ  } : _
        { _≤_ } : A → B → Type rℓ
        _≤?_    : Decidable _≤_

    _≥?_ = flip _≤?_

open DecOrder ⦃...⦄ public
