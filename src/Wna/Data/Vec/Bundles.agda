{-# OPTIONS --without-K --safe #-}

module Wna.Data.Vec.Bundles where

open import Agda.Builtin.Bool   using (true; false)
open import Agda.Builtin.Nat    using (zero; suc; _==_)
open import Wna.Class.Foldable  using (Foldable; module MkFoldable)
open import Wna.Data.Vec.Base

foldable : ∀{aℓ n} → Foldable (λ A → Vec {aℓ} A n)
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
