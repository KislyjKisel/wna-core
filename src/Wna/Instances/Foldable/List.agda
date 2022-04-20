{-# OPTIONS --without-K --safe #-}

module Wna.Instances.Foldable.List where

open import Data.List.Base
open import Wna.Class.Foldable using (Foldable; module MkFoldable)

List-Foldable : ∀{a} → Foldable (List {a})
List-Foldable = record
    { fold     = Mk.foldr⇒fold foldr
    ; foldl    = foldl
    ; foldr    = foldr
    ; foldMap  = Mk.foldr⇒foldMap foldr
    ; toList   = λ x → x
    ; is-empty = null
    ; length   = length
    ; _∈ᵇ_     = Mk.foldr⇒_∈ᵇ_ foldr
    }
    where module Mk = MkFoldable List
