{-# OPTIONS --without-K --safe #-}

module Wna.Data.List.Bundles where

open import Wna.Class.Foldable       using (Foldable; module MkFoldable)
open import Wna.Class.RawApplicative using (RawApplicative)
open import Wna.Class.RawFunctor     using (RawFunctor; module MkRawFunctor)
open import Wna.Class.Traversable    using (Traversable; module MkTraversable)
open import Wna.Data.List.Base
open import Wna.Primitive

rawFunctor : ∀{ℓ} → RawFunctor (List {ℓ})
rawFunctor = MkRawFunctor.from:<$> map

foldable : ∀{ℓ} → Foldable (List {ℓ})
foldable = record
    { foldl    = foldl
    ; foldr    = foldr
    ; fold     = Mk.foldr⇒fold foldr
    ; foldMap  = Mk.foldr⇒foldMap foldr
    ; toList   = λ x → x
    ; is-empty = null
    ; length   = length
    ; _∈ᵇ_     = Mk.foldr⇒_∈ᵇ_ foldr
    }
    where module Mk = MkFoldable List

traversable : ∀{ℓ} → Traversable (List {ℓ})
traversable = MkTraversable.from:traverse′ List ⦃ rawFunctor ⦄ traverse
    where
    module App = Wna.Class.RawApplicative.Instanced
