{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Encode where

open import Wna.Data.Universe using (Universe; ⟦_⟧)

record Encode {uℓ aℓ} (U : Set uℓ) (A : Set aℓ) : Set ? where
    field
        overlap ⦃ universe ⦄ : Universe ? 0 U
        encode : A → ⟦ ⟧

open Encode ⦃...⦄ public
