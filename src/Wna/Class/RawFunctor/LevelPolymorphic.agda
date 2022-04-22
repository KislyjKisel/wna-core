{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawFunctor.LevelPolymorphic where

open import Function                using (const; flip)
open import Wna.Class.RawFunctor    using (RawFunctor)
open import Wna.Primitive

Fun′ : Typeω
Fun′ = ∀{a} → Type a → Type a

module FunctorFT′ (F : Fun′) where

    _<$>′_ : Typeω
    _<$>′_ = ∀{a} {A : Type a} {b} {B : Type b} → (A → B) → F A → F B

    _<$′_ : Typeω
    _<$′_ = ∀{a} {A : Type a} {b} {B : Type b} → A → F B → F A


record RawFunctor′ (F : Fun′) : Typeω where
    private module FT′ = FunctorFT′ F
    infixl 4 _<$>′_ _<$′_
    infixl 1 _<&>′_

    field
        _<$>′_ : FT′._<$>′_
        _<$′_  : FT′._<$′_

    fmap′ = _<$>′_

    _<&>′_ : ∀{a} {A : Type a} {b} {B : Type b} → F A → (A → B) → F B
    _<&>′_ = flip _<$>′_

    rawFunctor : ∀{a} → RawFunctor (F {a})
    rawFunctor = record
        { _<$>_ = _<$>′_
        ; _<$_  = _<$′_
        }


module MkRawFunctor′ {F : Fun′} where
    private module FT′ = FunctorFT′ F

    <$>′⇒<$′ : FT′._<$>′_ → FT′._<$′_ 
    <$>′⇒<$′ _<$>′_ = λ x y → const x <$>′ y

    from:<$>′ : FT′._<$>′_ → RawFunctor′ F
    from:<$>′ _<$>′_ = record
        { _<$>′_ = _<$>′_
        ; _<$′_  = <$>′⇒<$′ _<$>′_
        }
