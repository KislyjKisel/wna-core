{-# OPTIONS --without-K --safe #-}

module Wna.Class.Cast where

open import Wna.Primitive

record Cast_⇒_ {aℓ bℓ} (From : Type aℓ) (To : Type bℓ) : Type (aℓ ℓ⊔ bℓ) where
    field
        cast : From → To

open Cast_⇒_ ⦃...⦄ public
