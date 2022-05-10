{-# OPTIONS --without-K --safe #-}

module Wna.Data.List.Bundles where

open import Data.List.Base
open import Wna.Class.Foldable using (Foldable; module MkFoldable)

foldable : ∀{a} → Foldable (List {a})
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
