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

record DecOrder {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infix 4 _≤_ _≤?_ _≥?_
    field
        { rℓ  } : _
        { _≤_ } : A → B → Type rℓ
        _≤?_    : Decidable _≤_

    _≥?_ = flip _≤?_

module Instanced where
    open DecStrictOrder ⦃...⦄ public
        using (_<?_; _>?_)

    open DecOrder ⦃...⦄ public
        using (_≤?_; _≥?_)

-- todo: Mk* modules for DecStrictOrder and DecOrder, _>?_ and _≥?_ as fields
