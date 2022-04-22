{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo.Properties where

open import Algebra.Definitions                     using (LeftIdentity; RightIdentity; Identity)
open import Data.Product                            using (_,_)
open import Relation.Binary.PropositionalEquality   using (refl; _≡_)
open import Wna.Data.Endo
open import Wna.Primitive

module _ {aℓ} {A : Type aℓ} where

    _<>_-identityˡ : LeftIdentity {A = Endo A} _≡_ unit _<>_
    _<>_-identityˡ (mkEndo f) = refl

    _<>_-identityʳ : RightIdentity {A = Endo A} _≡_ unit _<>_
    _<>_-identityʳ (mkEndo f) = refl

    _<>_-identity : Identity {A = Endo A} _≡_ unit _<>_
    _<>_-identity = _<>_-identityˡ , _<>_-identityʳ
