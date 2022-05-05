{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Container.Bundles where

open import Data.Container.Core using (⟦_⟧)
open import Wna.Monad.Identity.Container.Base
open import Wna.Class.RawMonad using (RawMonad; module MkRawMonad)

rawMonad : ∀{ℓ} → RawMonad {aℓ = ℓ} ⟦ Identity {sℓ = ℓ} {pℓ = ℓ} ⟧
rawMonad = MkRawMonad.from:pure,>>= mkIdentity λ x f → f (runIdentity x)
