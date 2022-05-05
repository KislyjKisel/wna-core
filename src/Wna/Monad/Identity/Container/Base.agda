{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Container.Base where

open import Data.Container.Combinator using (id)
open import Data.Container.Core       using (Container; ⟦_⟧)
open import Data.Product              using (_,_)
open import Wna.Primitive

module _ {sℓ} {pℓ} where
    
    Identity : Container sℓ pℓ
    Identity = id

    runIdentity : ∀{aℓ} {A : Type aℓ} → ⟦ Identity ⟧ A → A
    runIdentity (_ , p) = p _

    mkIdentity : ∀{aℓ} {A : Type aℓ} → A → ⟦ Identity ⟧ A
    mkIdentity x = _ , λ _ → x
