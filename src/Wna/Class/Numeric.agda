{-# OPTIONS --without-K --safe #-}

module Wna.Class.Numeric where

open import Wna.Primitive

record Negate {aℓ} (A : Type aℓ) : Typeω where
    infixl 9 -_
    field
        {r} : _
        R   : Type r
        -_  : A → R

record Add {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 6 _+_
    field
        {r} : _
        R   : Type r
        _+_ : A → B → R

record Subtract {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 6 _-_
    field
        {r} : _
        R   : Type r
        _-_ : A → B → R

record Multiply {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _*_
    field
        {r} : _
        R   : Type r
        _*_ : A → B → R

record Divide {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _/_
    field
        {r} : _
        R   : Type r
        _/_ : A → B → R

record Modulo {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _%_
    field
        {r} : _
        R   : Type r
        _%_ : A → B → R

record Quotient {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _quot_
    field
        {r} : _
        R   : Type r
        _quot_ : A → B → R

record Remainder {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _rem_
    field
        {r} : _
        R   : Type r
        _rem_ : A → B → R

record Square {aℓ} (A : Type aℓ) : Typeω where
    infix 8 _²
    field
        {r} : _
        R   : Type r
        _²  : A → R

record Reciprocal {aℓ} (A : Type aℓ) : Typeω where
    infix 7 1/_
    field
        {r} : _
        R   : Type r
        1/_ : A → R

record Power {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 8 _^_
    field
        {r} : _
        R   : Type r
        _^_ : A → B → R

record Exponential {aℓ} (A : Type aℓ) : Typeω where
    field
        {r} : _
        R   : Type r
        exp : A → R

record Absolute {aℓ} (A : Type aℓ) : Typeω where
    field
        {r} : _
        R   : Type r
        abs : A → R

record Join {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 6 _∨_
    field
        {r} : _
        R   : Type r
        _∨_ : A → B → R

record Meet {aℓ bℓ} (A : Type aℓ) (B : Type bℓ) : Typeω where
    infixl 7 _∧_
    field
        {r} : _
        R   : Type r
        _∧_ : A → B → R

module Instanced where
    open Negate ⦃...⦄ public
        using (-_)

    open Add ⦃...⦄ public
        using (_+_)

    open Subtract ⦃...⦄ public
        using (_-_)

    open Multiply ⦃...⦄ public
        using (_*_)

    open Divide ⦃...⦄ public
        using (_/_)

    open Modulo ⦃...⦄ public
        using (_%_)

    open Quotient ⦃...⦄ public
        using (_quot_)

    open Remainder ⦃...⦄ public
        using (_rem_)

    open Square ⦃...⦄ public
        using (_²)

    open Power ⦃...⦄ public
        using (_^_)

    open Exponential ⦃...⦄ public
        using (exp)

    open Absolute ⦃...⦄ public
        using (abs)

    open Join ⦃...⦄ public
        using (_∨_)

    open Meet ⦃...⦄ public
        using (_∧_)

    open Reciprocal ⦃...⦄ public
        using (1/_)
