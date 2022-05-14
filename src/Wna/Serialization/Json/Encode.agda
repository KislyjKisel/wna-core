{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Json.Encode where

open import Wna.Serialization.Json.Value using (Value)
open import Wna.Primitive

record Encode {ℓ} (A : Type ℓ) : Type ℓ where
    field
        encode : A → Value

module Instanced where
    open Encode ⦃...⦄ public
        using (encode)
