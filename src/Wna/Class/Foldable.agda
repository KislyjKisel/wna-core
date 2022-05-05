{-# OPTIONS --without-K --safe #-}

module Wna.Class.Foldable where

open import Agda.Builtin.List       using (List; []; _∷_)
open import Agda.Builtin.Nat        using ()                        renaming (Nat to ℕ)
open import Data.Bool.Base          using (Bool; true; false; _∨_)
open import Function.Base           using (id; flip; _∘′_)
open import Wna.Class.RawEquality   using (RawEquality)
open import Wna.Class.RawMonoid     using (RawMonoid)
open import Wna.Primitive

module FoldableFT {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    foldl    = {A : Type ℓ₁} → ∀{bℓ} {B : Type bℓ} → (B → A → B) → B → T A → B
    foldr    = {A : Type ℓ₁} → ∀{bℓ} {B : Type bℓ} → (A → B → B) → B → T A → B
    fold     = {A : Type ℓ₁} → ⦃ _ : RawMonoid A ⦄ → T A → A
    foldMap  = {A : Type ℓ₁} → ∀{bℓ} {B : Type bℓ} → ⦃ _ : RawMonoid B ⦄ → (A → B) → T A → B
    toList   = {A : Type ℓ₁} → T A → List A
    is-empty = {A : Type ℓ₁} → T A → Bool
    length   = {A : Type ℓ₁} → T A → ℕ
    _∈ᵇ_     =  ∀{aℓ} {A : Type aℓ} → A → {B : Type ℓ₁} → ⦃ _ : RawEquality A B ⦄ → T B → Bool

record Foldable {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) : Typeω where
    private module FT = FoldableFT T
    infix 4 _∈ᵇ_
    field
        foldl    : FT.foldl
        foldr    : FT.foldr
        fold     : FT.fold
        foldMap  : FT.foldMap
        toList   : FT.toList
        is-empty : FT.is-empty
        length   : FT.length
        _∈ᵇ_     : FT._∈ᵇ_

open Foldable ⦃...⦄ public

module MkFoldable {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    module FT = FoldableFT T

    foldr⇒foldl : FT.foldr → FT.foldl
    foldr⇒foldl foldr = λ f z t → foldr (λ x k → k ∘′ (flip f x)) id t z

    foldl⇒foldr : FT.foldl → FT.foldr
    foldl⇒foldr foldl f z t = foldl (λ k x → k ∘′ f x ) id t z

    foldr⇒fold : FT.foldr → FT.fold
    foldr⇒fold foldr ⦃ rawMonoid ⦄ = foldr mappend mempty
        where open RawMonoid rawMonoid

    foldr⇒foldMap : FT.foldr → FT.foldMap
    foldr⇒foldMap foldr ⦃ rawMonoid ⦄ f = foldr (mappend ∘′ f) mempty
        where open RawMonoid rawMonoid

    foldMap⇒fold : FT.foldMap → FT.fold
    foldMap⇒fold foldMap = foldMap id

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
        ; fold     = foldr⇒fold foldr
        ; foldMap  = foldr⇒foldMap foldr
        ; toList   = foldr⇒toList foldr
        ; is-empty = foldr⇒is-empty foldr
        ; length   = foldr⇒length foldr
        ; _∈ᵇ_     = foldr⇒_∈ᵇ_ foldr
        }

    from:foldl : FT.foldl → Foldable T
    from:foldl foldl = record
        { foldl    = foldl
        ; foldr    = foldl⇒foldr foldl
        ; fold     = foldr⇒fold (foldl⇒foldr foldl)
        ; foldMap  = foldr⇒foldMap (foldl⇒foldr foldl)
        ; toList   = foldl⇒toList foldl
        ; is-empty = foldl⇒is-empty foldl
        ; length   = foldl⇒length foldl
        ; _∈ᵇ_     = foldl⇒_∈ᵇ_ foldl
        }
 