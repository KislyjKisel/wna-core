{-# OPTIONS --without-K --safe #-}

module Wna.Class.Cast where

open import Wna.Primitive

record Cast[_⇒_] {aℓ bℓ} (From : Type aℓ) (To : Type bℓ) : Type (aℓ ℓ⊔ bℓ) where
    field
        cast : From → To

open Cast[_⇒_] ⦃...⦄ public
    using (cast)
