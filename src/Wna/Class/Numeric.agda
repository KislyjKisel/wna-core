{-# OPTIONS --without-K --safe #-}

module Wna.Class.Numeric where

open import Wna.Primitive

record Negate {aℓ} (A : Type aℓ) : Typeω where
    infixl 9 -_
    field
        {r} : _
        R   : Type r
        -_  : A → R

open Negate ⦃...⦄ public

record Add {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 6 _+_
    field
        {r} : _
        R   : Type r
        _+_ : A → B → R

open Add ⦃...⦄ public

record Subtract {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 6 _-_
    field
        {r} : _
        R   : Type r
        _-_ : A → B → R

open Subtract ⦃...⦄ public

record Multiply {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _*_
    field
        {r} : _
        R   : Type r
        _*_ : A → B → R

open Multiply ⦃...⦄ public

record Divide {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _/_
    field
        {r} : _
        R   : Type r
        _/_ : A → B → R

open Divide ⦃...⦄ public

record Square {aℓ} (A : Type aℓ) : Typeω where
    infixl 8 _²
    field
        {r} : _
        R   : Type r
        _²  : A → R

open Square ⦃...⦄ public

record Inverse {aℓ} (A : Type aℓ) : Typeω where
    infixl 8 _⁻¹
    field
        {r} : _
        R   : Type r
        _⁻¹ : A → R

open Inverse ⦃...⦄ public

record Power {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 8 _^_
    field
        {r} : _
        R   : Type r
        _^_ : A → B → R

open Power ⦃...⦄ public

record Exponential {aℓ} (A : Type aℓ) : Typeω where
    field
        {r} : _
        R   : Type r
        exp : A → R

open Exponential ⦃...⦄ public

record Absolute {aℓ} (A : Type aℓ) : Typeω where
    field
        {r} : _
        R   : Type r
        abs : A → R

open Absolute ⦃...⦄ public

record Join {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 6 _∨_
    field
        {r} : _
        R   : Type r
        _∨_ : A → B → R

open Join ⦃...⦄ public

record Meet {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _∧_
    field
        {r} : _
        R   : Type r
        _∧_ : A → B → R

open Meet ⦃...⦄ public
