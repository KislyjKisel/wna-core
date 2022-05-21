{-# OPTIONS --without-K --safe #-}

module Wna.Class.Numeric where

open import Wna.Primitive
open import Relation.Unary.Properties using (U?)
open import Relation.Unary using (Pred; Decidable)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Function.Base using (const)

-- todo: ?? dependent + constrained classes

record Negate {aℓ} (A : Type aℓ) : Typeω where
    infixl 9 -_
    field
        {rℓ}  : _
        {R}   : A → Type rℓ
        {pℓ}  : _
        {P}   : Pred A pℓ
        P?    : Decidable P
        -_⟨_⟩ : (x : A) → P x → R x

    -_ : (x : A) → ⦃ _ : True (P? x) ⦄ → R x
    -_ x ⦃ t ⦄ = - x ⟨ toWitness t ⟩

mkNegate‵ : ∀{aℓ} {A : Type aℓ} {rℓ} {R : A → Type rℓ} → ((x : A) → R x) → Negate A
mkNegate‵ -_ = record { P? = U? ; -_⟨_⟩ = λ x _ → - x }

mkNegate‵′ : ∀{aℓ} {A : Type aℓ} {rℓ} {R : Type rℓ} → (A → R) → Negate A
mkNegate‵′ -′_ = record { P? = U? ; -_⟨_⟩ = λ x _ → -′ x }

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

record Modulo {aℓ bℓ} (A : Type aℓ) (B : A → Type bℓ) : Typeω where
    infixl 7 _%_
    field
        {rℓ}   : _
        {R}    : (x : A) → (y : B x) → Type rℓ
        {pℓ}   : _
        {P}    : (x : A) → (y : B x) → Type pℓ
        P?     : (x : A) → (y : B x) → Dec (P x y)
        _%_⟨_⟩ : (x : A) → (y : B x) → .(P x y) → R x y
    
    _%_ : (x : A) → (y : B x) → .⦃ _ : True (P? x y) ⦄ → R x y
    _%_ x y ⦃ t ⦄ = x % y ⟨ toWitness t ⟩

mkModulo′ : ∀{aℓ bℓ} {A : Type aℓ} {B : Type bℓ} {rℓ} {R : Type rℓ} →
            ∀{pℓ} {P : A → B → Type pℓ} → ((x : A) → (y : B) → .(P x y) → R) →
            ((x : A) → (y : B) → Dec (P x y)) → Modulo A (const B)
mkModulo′ _%_⟨_⟩ P? = record { P? = P? ; _%_⟨_⟩ = _%_⟨_⟩ }

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
        using (-_; -_⟨_⟩)

    open Add ⦃...⦄ public
        using (_+_)

    open Subtract ⦃...⦄ public
        using (_-_)

    open Multiply ⦃...⦄ public
        using (_*_)

    open Divide ⦃...⦄ public
        using (_/_)

    open Modulo ⦃...⦄ public
        using (_%_; _%_⟨_⟩)

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
