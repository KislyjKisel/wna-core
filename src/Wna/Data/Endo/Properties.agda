{-# OPTIONS --without-K --safe #-}

module Wna.Data.Endo.Properties where

open import Wna.Data.Endo
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Algebra.Definitions using (LeftIdentity; RightIdentity; Identity)
open import Data.Product using (_,_)

module _ {aℓ} {A : Set aℓ} where

    <>-identityˡ : LeftIdentity {A = Endo A} _≡_ unit _<>_
    <>-identityˡ (mkEndo f) = refl

    <>-identityʳ : RightIdentity {A = Endo A} _≡_ unit _<>_
    <>-identityʳ (mkEndo f) = refl

    <>-identity : Identity {A = Endo A} _≡_ unit _<>_
    <>-identity = <>-identityˡ , <>-identityʳ
