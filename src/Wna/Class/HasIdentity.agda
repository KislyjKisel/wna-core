{-# OPTIONS --without-K --safe #-}

module Wna.Class.HasIdentity where

open import Algebra.Definitions                     using (Identity)
open import Relation.Binary.PropositionalEquality   using (_≡_)
open import Wna.Primitive

record HasIdentity {aℓ} {A : Type aℓ} (_⋆_ : A → A → A) : Type aℓ where
    field
        e     : A
        proof : Identity _≡_ e _⋆_
