{-# OPTIONS --without-K --safe #-}

module Wna.Class.Numeric where

open import Level using (Setω)

record Negate {aℓ} (A : Set aℓ) : Setω where
    infixl 9 -_
    field
        {r} : _
        R   : Set r
        -_  : A → R

open Negate ⦃...⦄ public

record Add {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    infixl 6 _+_
    field
        {r} : _
        R   : Set r
        _+_ : A → B → R

open Add ⦃...⦄ public

record Subtract {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    infixl 6 _-_
    field
        {r} : _
        R   : Set r
        _-_ : A → B → R

open Subtract ⦃...⦄ public

record Multiply {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    infixl 7 _*_
    field
        {r} : _
        R   : Set r
        _*_ : A → B → R

open Multiply ⦃...⦄ public

record Divide {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    infixl 7 _/_
    field
        {r} : _
        R   : Set r
        _/_ : A → B → R

open Divide ⦃...⦄ public

record Square {aℓ} (A : Set aℓ) : Setω where
    infixl 8 _²
    field
        {r} : _
        R   : Set r
        _²  : A → R

open Square ⦃...⦄ public

record Power {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    field
        {r} : _
        R   : Set r
        _^_ : A → B → R

open Power ⦃...⦄ public

record Exponential {aℓ} (A : Set aℓ) : Setω where
    field
        {r} : _
        R   : Set r
        exp : A → R

open Exponential ⦃...⦄ public

record Absolute {aℓ} (A : Set aℓ) : Setω where
    field
        {r} : _
        R   : Set r
        abs : A → R

open Absolute ⦃...⦄ public

record Join {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    field
        {r} : _
        R   : Set r
        _∨_ : A → B → R

open Join ⦃...⦄ public

record Meet {aℓ bℓ} (A : Set aℓ) (B : Set bℓ) : Setω where
    field
        {r} : _
        R   : Set r
        _∧_ : A → B → R

open Meet ⦃...⦄ public
