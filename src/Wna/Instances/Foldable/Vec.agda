{-# OPTIONS --without-K --safe #-}

module Wna.Instances.Foldable.Vec where

open import Data.Vec.Base
open import Wna.Class.Foldable using (Foldable; module MkFoldable)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (zero; suc; _==_)

List-Foldable : ∀{aℓ n} → Foldable (λ A → Vec {aℓ} A n)
List-Foldable {aℓ} {n} = record
    { fold     = Mk.foldr⇒fold foldr′
    ; foldl    = foldl′
    ; foldr    = foldr′
    ; foldMap  = Mk.foldr⇒foldMap foldr′
    ; toList   = toList
    ; is-empty = λ _ → n == zero
    ; length   = λ _ → n
    ; _∈ᵇ_     = Mk.foldr⇒_∈ᵇ_ foldr′
    }
    where module Mk = MkFoldable (λ A → Vec {aℓ} A n)
