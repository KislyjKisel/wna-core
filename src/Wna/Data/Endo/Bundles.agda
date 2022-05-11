{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo.Bundles where

open import Wna.Class.RawMonoid using (RawMonoid)
open import Wna.Data.Endo       using (Endo; unit; _<>_)
open import Wna.Primitive

rawMonoid : ∀{ℓ} {A : Type ℓ} → RawMonoid (Endo A)
rawMonoid = record
    { mappend = _<>_
    ; mempty  = unit
    }
