{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Bundles where

open import Data.Container.Core  using (Container; map; ⟦_⟧)
open import Wna.Class.RawFunctor using (RawFunctor; module MkRawFunctor)

rawFunctor : ∀{s p ℓ} {C : Container s p} → RawFunctor {aℓ = ℓ} ⟦ C ⟧
rawFunctor {C = C} = record
    { _<$>_ = map
    ; _<$_  = MkRawFunctor.<$>⇒<$ {F = ⟦ C ⟧} map
    }
