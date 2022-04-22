{-# OPTIONS --without-K --safe #-}

module Wna.Class.HasIdentity where

open import Algebra.Definitions using (Identity)
open import Relation.Binary.PropositionalEquality using (_≡_)

record HasIdentity {aℓ} {A : Set aℓ} (_⋆_ : A → A → A) : Set aℓ where
    field
        e     : A
        proof : Identity _≡_ e _⋆_
