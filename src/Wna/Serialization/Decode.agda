{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Decode where

open import Data.String.Base using (String)
open import Level            using (Lift; lift)
open import Effect.Monad.Except using (Except)

record Decode {eℓ aℓ} (E : Set eℓ) (A : Set aℓ) : Typeω where
    field
        decode : Value → Except (Lift _ String) A

open Decode ⦃...⦄ public