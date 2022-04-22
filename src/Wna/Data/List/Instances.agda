{-# OPTIONS --without-K --safe #-}

module Wna.Data.List.Instances where

open import Data.List.Base
open import Wna.Class.Foldable using (Foldable; module MkFoldable)

List-Foldable : ∀{a} → Foldable (List {a})
List-Foldable = record
    { foldl    = foldl
    ; foldr    = foldr
    ; toList   = λ x → x
    ; is-empty = null
    ; length   = length
    ; _∈ᵇ_     = Mk.foldr⇒_∈ᵇ_ foldr
    }
    where module Mk = MkFoldable List
