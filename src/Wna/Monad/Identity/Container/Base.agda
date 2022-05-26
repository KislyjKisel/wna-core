{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Container.Base where

open import Data.Container.Combinator using (id)
open import Data.Container.Core       using (Container; ⟦_⟧)
open import Wna.Data.Container.Properties as Ccp using ()
open import Data.Product              using (_,_)
open import Wna.Primitive

module _ {ℓ} where
    
    Identity : Container ℓ ℓ
    Identity = id

    runIdentity : ∀{aℓ} {A : Type aℓ} → ⟦ Identity ⟧ A → A
    runIdentity = Ccp.id-from

    mkIdentity : ∀{aℓ} {A : Type aℓ} → A → ⟦ Identity ⟧ A
    mkIdentity = Ccp.id-to
