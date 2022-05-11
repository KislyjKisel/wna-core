{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo.Base where

open import Wna.Primitive

record Endo {aℓ} (A : Type aℓ) : Type aℓ where
    constructor mkEndo
    field
        appEndo : A → A

open Endo public
    using (appEndo)

unit : ∀{aℓ} {A : Type aℓ} → Endo A
unit = mkEndo λ x → x 

_<>_ : ∀{aℓ} {A : Type aℓ} → Endo A → Endo A → Endo A
(mkEndo f) <> (mkEndo g) = mkEndo (λ x → f (g x))
