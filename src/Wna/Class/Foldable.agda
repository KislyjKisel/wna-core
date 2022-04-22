{-# OPTIONS --without-K --safe #-}

module Wna.Class.Foldable where

open import Wna.Primitive
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Wna.Class.RawEquality using (RawEquality)
open import Function.Base using (id; flip; _∘′_)

module FoldableFT {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    foldl = {A : Type ℓ₁} → ∀{b} {B : Type b} → (B → A → B) → B → T A → B
    foldr = {A : Type ℓ₁} → ∀{b} {B : Type b} → (A → B → B) → B → T A → B
    toList = {A : Type ℓ₁} → T A → List A
    is-empty = {A : Type ℓ₁} → T A → Bool
    length = {A : Type ℓ₁} → T A → ℕ
    _∈ᵇ_ =  ∀{aℓ} {A : Set aℓ} → A → {B : Type ℓ₁} → ⦃ _ : RawEquality A B ⦄ → T B → Bool

record Foldable {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) : Typeω where
    module FT = FoldableFT T
    field
        foldl    : FT.foldl
        foldr    : FT.foldr
        toList   : FT.toList
        is-empty : FT.is-empty
        length   : FT.length
        _∈ᵇ_     : FT._∈ᵇ_


module MkFoldable {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    module FT = FoldableFT T

    foldr⇒foldl : FT.foldr → FT.foldl
    foldr⇒foldl foldr = λ f z t → foldr (λ x k → k ∘′ (flip f x)) id t z

    foldl⇒foldr : FT.foldl → FT.foldr
    foldl⇒foldr foldl f z t = foldl (λ k x → k ∘′ f x ) id t z

    foldr⇒toList : FT.foldr → FT.toList
    foldr⇒toList foldr = foldr _∷_ []

    foldl⇒toList : FT.foldl → FT.toList
    foldl⇒toList foldl = foldl (flip _∷_) []

    foldr⇒is-empty : FT.foldr → FT.is-empty
    foldr⇒is-empty foldr = foldr (λ _ _ → false) true

    foldl⇒is-empty : FT.foldl → FT.is-empty
    foldl⇒is-empty foldl = foldl (λ _ _ → false) true

    foldr⇒length : FT.foldr → FT.length
    foldr⇒length foldr = foldr (λ _ c → ℕ.suc c) 0

    foldl⇒length : FT.foldl → FT.length
    foldl⇒length foldl = foldl (λ c _ → ℕ.suc c) 0

    foldr⇒_∈ᵇ_ : FT.foldr → FT._∈ᵇ_
    foldr⇒_∈ᵇ_ foldr x ⦃ Eq ⦄ = foldr (λ y e → e ∨ (x ≡ᵇ y)) false
        where open RawEquality Eq

    foldl⇒_∈ᵇ_ : FT.foldl → FT._∈ᵇ_
    foldl⇒_∈ᵇ_ foldl x ⦃ Eq ⦄ = foldl (λ e y → e ∨ (x ≡ᵇ y)) false
        where open RawEquality Eq

    from:foldr : FT.foldr → Foldable T
    from:foldr foldr = record
        { foldl    = foldr⇒foldl foldr
        ; foldr    = foldr
        ; toList   = foldr⇒toList foldr
        ; is-empty = foldr⇒is-empty foldr
        ; length   = foldr⇒length foldr
        ; _∈ᵇ_     = foldr⇒_∈ᵇ_ foldr
        }

    from:foldl : FT.foldl → Foldable T
    from:foldl foldl = record
        { foldl    = foldl
        ; foldr    = foldl⇒foldr foldl
        ; toList   = foldl⇒toList foldl
        ; is-empty = foldl⇒is-empty foldl
        ; length   = foldl⇒length foldl
        ; _∈ᵇ_     = foldl⇒_∈ᵇ_ foldl
        }

open Foldable ⦃...⦄ public
 