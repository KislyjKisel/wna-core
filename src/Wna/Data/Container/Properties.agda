{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Properties where

open import Data.Container.Combinator            as Cc    using ()
open import Data.Container.Combinator.Properties          using (module Composition)
open import Data.Container.Core                           using (Container; ⟦_⟧)
open import Function.Base                                 using (_$_; _∘′_)
open import Function.Equality                    as FunEq using ()
open import Function.Inverse                              using (Inverse)
open import Wna.Primitive

module _ {s₁ℓ p₁ℓ s₂ℓ p₂ℓ} (C₁ : Container s₁ℓ p₁ℓ) (C₂ : Container s₂ℓ p₂ℓ) where

    module _ {aℓ} {A : Type aℓ} where
        private
            ∘-correct = Composition.correct C₁ C₂ {X = A}
        
        open FunEq.Π (Inverse.to ∘-correct) public
            using () renaming (_⟨$⟩_ to [c∘c]⇒c[c])

        open FunEq.Π (Inverse.from ∘-correct) public
            using () renaming (_⟨$⟩_ to c[c]⇒[c∘c])
