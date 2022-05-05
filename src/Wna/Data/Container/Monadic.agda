{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Monadic where

open import Data.Container.Core using (Container; ⟦_⟧)
open import Data.Container.Combinator as Cc using ()
open import Data.Container.Combinator.Properties using (module Composition)
open import Function.Inverse using (Inverse)
open import Function.Equality as FunEq using ()
open import Function.Base using (_$_; _∘′_)
open import Wna.Primitive

∘-pure : ∀{ℓ} {C₁ C₂ : Container ℓ ℓ} → (∀{A : Type ℓ} → A → ⟦ C₁ ⟧ A) →
         {A : Type ℓ} → ⟦ C₂ ⟧ A → ⟦ C₁ Cc.∘ C₂ ⟧ A
∘-pure {C₁ = C₁} {C₂ = C₂} pure {A = A} = c[c]⇒[c∘c] ∘′ pure
    where
    open FunEq.Π (Inverse.from $ Composition.correct C₁ C₂ {X = A})
        using () renaming (_⟨$⟩_ to c[c]⇒[c∘c])
