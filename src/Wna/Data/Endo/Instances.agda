{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo.Instances where

open import Wna.Class.HasIdentity       using (HasIdentity)
open import Wna.Data.Endo
open import Wna.Data.Endo.Properties
open import Wna.Primitive

instance
    _<>_-HasIdentity : ∀{aℓ} {A : Type aℓ} → HasIdentity {A = Endo A} _<>_
    _<>_-HasIdentity = record
        { e     = unit
        ; proof = _<>_-identity
        }
