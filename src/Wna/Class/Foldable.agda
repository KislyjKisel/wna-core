{-# OPTIONS --without-K --safe #-}

module Wna.Class.Foldable where

open import Agda.Builtin.List             using (List; []; _∷_)
open import Agda.Builtin.Nat              using ()                        renaming (Nat to ℕ)
open import Data.Bool.Base                using (Bool; true; false; _∨_)
open import Function.Base                 using (id; flip; _∘′_; _$′_)
open import Wna.Class.RawEquality         using (RawEquality)
open import Wna.Class.RawMonoid           using (RawMonoid; dual)
open import Wna.Data.Endo         as Endo using (Endo; mkEndo; appEndo)
open import Wna.Primitive

-- todo
-- bℓ ≠ ℓ₁ --> can't? make foldMap from traverse, can't make foldable from traversable
-- bℓ = ℓ₁ --> can't use types with ℓ ≠ ℓ₁, can't use non-ℓ-polymorphic types in folds (smaller only with lift)

module _ {ℓ₁ ℓ₂} (T : Type ℓ₁ → Type ℓ₂) where
    module FoldableFT where
        foldl    = {A : Type ℓ₁} → ∀{bℓ} {B : Type bℓ} → (B → A → B) → B → T A → B
        foldr    = {A : Type ℓ₁} → ∀{bℓ} {B : Type bℓ} → (A → B → B) → B → T A → B
        fold     = {A : Type ℓ₁} → ⦃ _ : RawMonoid A ⦄ → T A → A
        foldMap  = {A : Type ℓ₁} → ∀{bℓ} {B : Type bℓ} → ⦃ _ : RawMonoid B ⦄ → (A → B) → T A → B
        toList   = {A : Type ℓ₁} → T A → List A
        is-empty = {A : Type ℓ₁} → T A → Bool
        length   = {A : Type ℓ₁} → T A → ℕ
        _∈ᵇ_     =  ∀{aℓ} {A : Type aℓ} → A → {B : Type ℓ₁} → ⦃ _ : RawEquality A B ⦄ → T B → Bool

    record Foldable : Typeω where
        infix 4 _∈ᵇ_
        field
            foldl    : FoldableFT.foldl
            foldr    : FoldableFT.foldr
            fold     : FoldableFT.fold
            foldMap  : FoldableFT.foldMap
            toList   : FoldableFT.toList
            is-empty : FoldableFT.is-empty
            length   : FoldableFT.length
            _∈ᵇ_     : FoldableFT._∈ᵇ_

    module MkFoldable where

        foldr⇒foldl : FoldableFT.foldr → FoldableFT.foldl
        foldr⇒foldl foldr = λ f z t → foldr (λ x k → k ∘′ (flip f x)) id t z

        foldl⇒foldr : FoldableFT.foldl → FoldableFT.foldr
        foldl⇒foldr foldl f z t = foldl (λ k x → k ∘′ f x ) id t z

        foldr⇒fold : FoldableFT.foldr → FoldableFT.fold
        foldr⇒fold foldr ⦃ rawMonoid ⦄ = foldr mappend mempty
            where open RawMonoid rawMonoid

        foldr⇒foldMap : FoldableFT.foldr → FoldableFT.foldMap
        foldr⇒foldMap foldr ⦃ rawMonoid ⦄ f = foldr (mappend ∘′ f) mempty
            where open RawMonoid rawMonoid

        foldMap⇒fold : FoldableFT.foldMap → FoldableFT.fold
        foldMap⇒fold foldMap = foldMap id

        foldMap⇒foldl : FoldableFT.foldMap → FoldableFT.foldl
        foldMap⇒foldl foldMap f z t = (appEndo $′ foldMap ⦃ dual $′ Endo.rawMonoid ⦄ (λ x → mkEndo $′ flip f x) t) z

        foldr⇒toList : FoldableFT.foldr → FoldableFT.toList
        foldr⇒toList foldr = foldr _∷_ []

        foldl⇒toList : FoldableFT.foldl → FoldableFT.toList
        foldl⇒toList foldl = foldl (flip _∷_) []

        foldr⇒is-empty : FoldableFT.foldr → FoldableFT.is-empty
        foldr⇒is-empty foldr = foldr (λ _ _ → false) true

        foldl⇒is-empty : FoldableFT.foldl → FoldableFT.is-empty
        foldl⇒is-empty foldl = foldl (λ _ _ → false) true

        foldr⇒length : FoldableFT.foldr → FoldableFT.length
        foldr⇒length foldr = foldr (λ _ c → ℕ.suc c) 0

        foldl⇒length : FoldableFT.foldl → FoldableFT.length
        foldl⇒length foldl = foldl (λ c _ → ℕ.suc c) 0

        foldr⇒_∈ᵇ_ : FoldableFT.foldr → FoldableFT._∈ᵇ_
        foldr⇒_∈ᵇ_ foldr x ⦃ Eq ⦄ = foldr (λ y e → e ∨ (x ≡ᵇ y)) false
            where open RawEquality Eq

        foldl⇒_∈ᵇ_ : FoldableFT.foldl → FoldableFT._∈ᵇ_
        foldl⇒_∈ᵇ_ foldl x ⦃ Eq ⦄ = foldl (λ e y → e ∨ (x ≡ᵇ y)) false
            where open RawEquality Eq

        from:foldr : FoldableFT.foldr → Foldable
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

        from:foldl : FoldableFT.foldl → Foldable
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

        from:foldMap : FoldableFT.foldMap → Foldable
        from:foldMap foldMap = from:foldl (foldMap⇒foldl foldMap)

module Instanced where
    open Foldable ⦃...⦄ public
        using (foldl; foldr; fold; foldMap)
  