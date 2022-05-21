{-# OPTIONS --without-K --safe #-}

module Wna.Data.Vec.Bundles where

open import Agda.Builtin.Bool   using (true; false)
open import Agda.Builtin.Nat    using (zero; suc; _==_)
open import Wna.Class.Foldable  using (Foldable; module MkFoldable)
open import Wna.Class.Traversable using (Traversable; module MkTraversable)
open import Wna.Class.RawFunctor using (RawFunctor; module MkRawFunctor)
open import Wna.Data.Vec.Base

rawFunctor : ∀{aℓ n} → RawFunctor (λ A → Vec {a = aℓ} A n)
rawFunctor = MkRawFunctor.from:<$> map

foldable : ∀{aℓ n} → Foldable (λ A → Vec {a = aℓ} A n)
foldable {aℓ} {n} = record
    { foldl    = foldl′
    ; foldr    = foldr′
    ; fold     = Mk.foldr⇒fold foldr′
    ; foldMap  = Mk.foldr⇒foldMap foldr′
    ; toList   = toList
    ; is-empty = λ _ → n == zero
    ; length   = λ _ → n
    ; _∈ᵇ_     = Mk.foldr⇒_∈ᵇ_ foldr′
    }
    where module Mk = MkFoldable (λ A → Vec {aℓ} A n)

traversable : ∀{aℓ n} → Traversable (λ A → Vec {a = aℓ} A n)
traversable = MkTraversable.from:traverse′ _ ⦃ rawFunctor ⦄ traverse
