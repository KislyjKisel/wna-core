{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Conversion where

open import Data.Container.Combinator            as Cc    using ()
open import Data.Container.Combinator.Properties
open import Data.Container.Core                           using (Container; ⟦_⟧)
open import Data.Empty                                    using (⊥-elim)
open import Data.Product                                  using (proj₁; _×_; _,_)
open import Data.Sum                             as ⊎     using (inj₁; inj₂)
open import Function.Base                                 using (const; id; _$′_; _∘′_)
open import Function.Equality                    as FunEq using ()
open import Function.Inverse                              using (Inverse)
open import Wna.Primitive

-- todo: automatic data ↔ container conversion functions generation?
--       mb def abstract combinators (ac) and ac -> cont and ac -> data and (ac -> cont) ≗ (ac -> data)  

module _ {sℓ pℓ aℓ} {A : Type aℓ} where

    private
        id-correct = Identity.correct {sℓ} {pℓ} {aℓ} {X = A}
    
    open FunEq.Π (Inverse.to id-correct) public
        using () renaming (_⟨$⟩_ to id-from)

    open FunEq.Π (Inverse.from id-correct) public
        using () renaming (_⟨$⟩_ to id-to)

module _ {pℓ aℓ bℓ} {A : Type aℓ} {B : Type bℓ} where
    
    const-from : ⟦ Cc.const {p = pℓ} A ⟧ B → A
    const-from = proj₁

    const-to : A → ⟦ Cc.const {p = pℓ} A ⟧ B
    const-to x = x , (⊥-elim ∘′ unliftℓ)

module _ {s₁ℓ p₁ℓ s₂ℓ p₂ℓ} {C₁ : Container s₁ℓ p₁ℓ} {C₂ : Container s₂ℓ p₂ℓ}
         {aℓ} {A : Type aℓ}
         where

    private
        ∘-correct = Composition.correct C₁ C₂ {X = A}
    
    open FunEq.Π (Inverse.to ∘-correct) public
        using () renaming (_⟨$⟩_ to composition-from)

    open FunEq.Π (Inverse.from ∘-correct) public
        using () renaming (_⟨$⟩_ to composition-to)

module _ {s₁ℓ p₁ℓ s₂ℓ p₂ℓ} {C₁ : Container s₁ℓ p₁ℓ} {C₂ : Container s₂ℓ p₂ℓ}
         {aℓ} {A : Type aℓ}
         where

    product-from : ⟦ C₁ Cc.× C₂ ⟧ A → ⟦ C₁ ⟧ A × ⟦ C₂ ⟧ A
    product-from ((s₁ , s₂) , f) = (s₁ , f ∘′ inj₁) , (s₂ , f ∘′ inj₂)
    
    product-to : ⟦ C₁ ⟧ A × ⟦ C₂ ⟧ A → ⟦ C₁ Cc.× C₂ ⟧ A
    product-to ((s₁ , f₁) , (s₂ , f₂)) = (s₁ , s₂) , ⊎.[ f₁ , f₂ ]′

module _ {iℓ sℓ pℓ} {I : Type iℓ} {C : Container sℓ pℓ} {aℓ} {A : Type aℓ} where
    private
        const[]⟶-correct = ConstantExponentiation.correct {I = I} C {X = A}

    open FunEq.Π (Inverse.to const[]⟶-correct) public
        using () renaming (_⟨$⟩_ to constexp-from)

    open FunEq.Π (Inverse.from const[]⟶-correct) public
        using () renaming (_⟨$⟩_ to constexp-to)
