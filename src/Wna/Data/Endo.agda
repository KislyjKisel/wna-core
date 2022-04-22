{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo where

record Endo {aℓ} (A : Set aℓ) : Set aℓ where
    constructor mkEndo
    field
        appEndo : A → A

open Endo public

unit : ∀{aℓ} {A : Set aℓ} → Endo A
unit = mkEndo λ x → x 

_<>_ : ∀{aℓ} {A : Set aℓ} → Endo A → Endo A → Endo A
(mkEndo f) <> (mkEndo g) = mkEndo (λ x → f (g x))
