{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo.Instances where

open import Wna.Data.Endo
open import Wna.Data.Endo.Properties
open import Wna.Class.HasIdentity using (HasIdentity)

instance
    Endo-HasIdentity : ∀{aℓ} {A : Set aℓ} → HasIdentity {A = Endo A} _<>_
    Endo-HasIdentity = record
        { e     = unit
        ; proof = <>-identity
        }
