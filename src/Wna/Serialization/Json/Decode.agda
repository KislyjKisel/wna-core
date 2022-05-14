{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Json.Decode where

open import Data.String.Base                   using (String)
open import Level                              using (Lift; lift)
open import Wna.Primitive
open import Wna.Serialization.Json.Value       using (Value)
open import Wna.Monad.Except                   using (Except)

record Decode {ℓ} (A : Type ℓ) : Typeω where
    field
        {cℓ}       : _
        constraint : Value → Type cℓ
        decode     : (x : Value) → constraint x → A
        try-decode : Value → Except (Lift _ String) A

module Instanced where
    open Decode ⦃...⦄ public
        using (decode)

-- case (c? v) of λ where
--                 (inj₂ p) → Ex.pure $ d v p
--                 (inj₁  _) → Ex.raise $ lift err
--             }