{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawFunctor where

open import Function.Base using (const; flip)
open import Wna.Primitive

Fun : ∀ a → Type (ℓ↑ a)
Fun a = Type a → Type a

module FunctorFT {aℓ bℓ} (F : Type aℓ → Type bℓ) where

    _<$>_ : Type (ℓ↑ aℓ ℓ⊔ bℓ)
    _<$>_ = ∀{A B : Type aℓ} → (A → B) → F A → F B

    _<$_ : Type (ℓ↑ aℓ ℓ⊔ bℓ)
    _<$_ = ∀{A B : Type aℓ} → A → F B → F A


record RawFunctor {aℓ bℓ} (F : Type aℓ → Type bℓ) : Type (ℓ↑ aℓ ℓ⊔ bℓ) where
    private module FT = FunctorFT F
    infixl 4 _<$>_ _<$_
    infixl 1 _<&>_

    field
        _<$>_ : FT._<$>_
        _<$_  : FT._<$_

    fmap = _<$>_

    _<&>_ : ∀{A B : Type aℓ} → F A → (A → B) → F B
    _<&>_ = flip _<$>_


module MkRawFunctor {aℓ bℓ} {F : Type aℓ → Type bℓ} where
    private module FT = FunctorFT F

    <$>⇒<$ : FT._<$>_ → FT._<$_
    <$>⇒<$ _<$>_ = λ x y → const x <$> y

    from:<$> : FT._<$>_ → RawFunctor {aℓ} {bℓ} F
    from:<$> _<$>_ = record
        { _<$>_ = _<$>_
        ; _<$_  = <$>⇒<$ _<$>_
        }
