{-# OPTIONS --without-K --safe #-}

module Wna.Class.Foldable where

open import Wna.Prelude
open import Wna.Class.Monoid using (Monoid; mkEndo; appEndo; mkDual; getDual)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using () renaming (Nat to ℕ)
open import Function.Base using (id; _∘′_; _$_; flip)
open import Wna.Class.Equality using (Equalityᵇ)
open import Wna.Instances.Monoid.Endo
open import Wna.Instances.Monoid.Dual

module FoldableFT {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    fold = {M : Type ℓ₁} → ⦃ _ : Monoid M ⦄ → T M → M
    foldl = {A : Type ℓ₁} → ∀{b} {B : Type b} → (B → A → B) → B → T A → B
    foldr = {A : Type ℓ₁} → ∀{b} {B : Type b} → (A → B → B) → B → T A → B
    foldMap = {A : Type ℓ₁} → ∀{mℓ} {M : Type mℓ} → ⦃ _ : Monoid M ⦄ → (A → M) → T A → M
    toList = {A : Type ℓ₁} → T A → List A
    is-empty = {A : Type ℓ₁} → T A → Bool
    length = {A : Type ℓ₁} → T A → ℕ
    _∈ᵇ_ =  {A : Type ℓ₁} → ⦃ _ : Equalityᵇ A ⦄ → A → T A → Bool

record Foldable {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) : Typeω where
    module FT = FoldableFT T
    field
        fold    : FT.fold
        foldl   : FT.foldl
        foldr   : FT.foldr
        foldMap : FT.foldMap
        toList   : FT.toList
        is-empty : FT.is-empty
        length   : FT.length
        _∈ᵇ_     : FT._∈ᵇ_


module MkFoldable {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    module FT = FoldableFT T

    foldMap⇒fold : FT.foldMap → FT.fold
    foldMap⇒fold foldMap = foldMap id

    foldMap⇒foldl : FT.foldMap → FT.foldl
    foldMap⇒foldl foldMap = λ f z t → appEndo (getDual (foldMap (mkDual ∘′ mkEndo ∘′ flip f) t)) z
        where
        instance
            _ = Endo-Monoid
            _ = Dual-Monoid

    foldMap⇒foldr : FT.foldMap → FT.foldr
    foldMap⇒foldr foldMap = λ f z t → appEndo (foldMap ⦃ Endo-Monoid ⦄ (λ x → mkEndo $ f x) t) z
        where module ME {a A} = Monoid (Endo-Monoid {a} {A})

    foldr⇒fold : FT.foldr → FT.fold
    foldr⇒fold foldr ⦃ M ⦄ = foldr _<>_ ε 
        where open Monoid M

    foldr⇒foldl : FT.foldr → FT.foldl
    foldr⇒foldl foldr = λ f z t → foldr (λ x k z' → k (f z x)) id t z

    foldr⇒foldMap : FT.foldr → FT.foldMap
    foldr⇒foldMap foldr ⦃ M ⦄ = λ f → foldr (_<>_ ∘′ f) ε
        where open Monoid M

    foldr⇒toList : FT.foldr → FT.toList
    foldr⇒toList foldr = λ t → foldr _∷_ [] t

    foldr⇒is-empty : FT.foldr → FT.is-empty
    foldr⇒is-empty foldr = foldr (λ _ _ → false) true 

    foldr⇒length : FT.foldr → FT.length
    foldr⇒length foldr = foldr (λ _ c → ℕ.suc c) 0

    foldr⇒_∈ᵇ_ : FT.foldr → FT._∈ᵇ_
    foldr⇒_∈ᵇ_ foldr ⦃ Eq ⦄ = λ x → foldr (λ e r → r ∨ e ≡ᵇ x ) false
        where open Equalityᵇ Eq

    from:foldr : FT.foldr → Foldable T
    from:foldr foldr = record
        { fold     = foldr⇒fold foldr
        ; foldl    = foldr⇒foldl foldr
        ; foldr    = foldr
        ; foldMap  = foldr⇒foldMap foldr
        ; toList   = foldr⇒toList foldr
        ; is-empty = foldr⇒is-empty foldr
        ; length   = foldr⇒length foldr
        ; _∈ᵇ_     = foldr⇒_∈ᵇ_ foldr
        }

open Foldable ⦃...⦄ public
