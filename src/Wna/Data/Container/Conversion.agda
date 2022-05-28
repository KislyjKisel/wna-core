{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Conversion where

open import Data.Container.Combinator            as Cc    using ()
open import Data.Container.Combinator.Properties
open import Data.Container.Core                  as C     using (Container; ⟦_⟧)
open import Data.Empty                                    using (⊥-elim)
open import Data.Product                                  using (proj₁; _×_; _,_)
open import Data.Sum                             as ⊎     using (inj₁; inj₂; _⊎_)
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

    id-map : ∀{s'ℓ p'ℓ bℓ} {B : Type bℓ} → (A → B) → ⟦ Cc.id ⟧ A → ⟦ Cc.id {s'ℓ} {p'ℓ} ⟧ B
    id-map = C.map

module _ {pℓ aℓ bℓ} {A : Type aℓ} {B : Type bℓ} where
    
    const-from : ⟦ Cc.const {p = pℓ} A ⟧ B → A
    const-from = proj₁

    const-to : A → ⟦ Cc.const {p = pℓ} A ⟧ B
    const-to x = x , (⊥-elim ∘′ unliftℓ)

const-map : ∀{pℓ p'ℓ aℓ bℓ cℓ} {A : Type aℓ} {B : Type bℓ} {C : Type cℓ} →
            (A → C) → ⟦ Cc.const {p = pℓ} A ⟧ B → ⟦ Cc.const {p = p'ℓ} C ⟧ B
const-map f = const-to ∘′ f ∘′ const-from

module _ {s₁ℓ p₁ℓ s₂ℓ p₂ℓ} {C₁ : Container s₁ℓ p₁ℓ} {C₂ : Container s₂ℓ p₂ℓ}
         {aℓ} {A : Type aℓ}
         where

    private
        composition-correct = Composition.correct C₁ C₂ {X = A}
    
    open FunEq.Π (Inverse.to composition-correct) public
        using () renaming (_⟨$⟩_ to composition-from)

    open FunEq.Π (Inverse.from composition-correct) public
        using () renaming (_⟨$⟩_ to composition-to)

composition-map : ∀{s₁ℓ p₁ℓ s₂ℓ p₂ℓ} {C₁ : Container s₁ℓ p₁ℓ} {C₂ : Container s₂ℓ p₂ℓ}
                  {aℓ bℓ} {A : Type aℓ} {B : Type bℓ} →
                  (⟦ C₁ ⟧ (⟦ C₂ ⟧ A) → ⟦ C₁ ⟧ (⟦ C₂ ⟧ B)) →
                  ⟦ C₁ Cc.∘ C₂ ⟧ A → ⟦ C₁ Cc.∘ C₂ ⟧ B
composition-map f = composition-to ∘′ f ∘′ composition-from

module _ {s₁ℓ p₁ℓ s₂ℓ p₂ℓ} {C₁ : Container s₁ℓ p₁ℓ} {C₂ : Container s₂ℓ p₂ℓ}
         {aℓ} {A : Type aℓ}
         where

    product-from : ⟦ C₁ Cc.× C₂ ⟧ A → ⟦ C₁ ⟧ A × ⟦ C₂ ⟧ A
    product-from ((s₁ , s₂) , f) = (s₁ , f ∘′ inj₁) , (s₂ , f ∘′ inj₂)
    
    product-to : ⟦ C₁ ⟧ A × ⟦ C₂ ⟧ A → ⟦ C₁ Cc.× C₂ ⟧ A
    product-to ((s₁ , f₁) , (s₂ , f₂)) = (s₁ , s₂) , ⊎.[ f₁ , f₂ ]′

product-map : ∀{s₁ℓ p₁ℓ s₂ℓ p₂ℓ} {C₁ : Container s₁ℓ p₁ℓ} {C₂ : Container s₂ℓ p₂ℓ}
              {aℓ bℓ} {A : Type aℓ} {B : Type bℓ} →
              (⟦ C₁ ⟧ A × ⟦ C₂ ⟧ A → ⟦ C₁ ⟧ B × ⟦ C₂ ⟧ B) →
              ⟦ C₁ Cc.× C₂ ⟧ A → ⟦ C₁ Cc.× C₂ ⟧ B
product-map f = product-to ∘′ f ∘′ product-from

module _ {s₁ℓ s₂ℓ pℓ} {C₁ : Container s₁ℓ pℓ} {C₂ : Container s₂ℓ pℓ}
         {aℓ} {A : Type aℓ}
         where

    private
        sum-correct = Sum.correct C₁ C₂ {X = A}

    open FunEq.Π (Inverse.to sum-correct) public
        using () renaming (_⟨$⟩_ to sum-from)

    open FunEq.Π (Inverse.from sum-correct) public
        using () renaming (_⟨$⟩_ to sum-to)   

sum-map : ∀{s₁ℓ s₂ℓ pℓ} {C₁ : Container s₁ℓ pℓ} {C₂ : Container s₂ℓ pℓ}
          {aℓ bℓ} {A : Type aℓ} {B : Type bℓ} →
          (⟦ C₁ ⟧ A ⊎ ⟦ C₂ ⟧ A → ⟦ C₁ ⟧ B ⊎ ⟦ C₂ ⟧ B) →
          ⟦ C₁ Cc.⊎ C₂ ⟧ A → ⟦ C₁ Cc.⊎ C₂ ⟧ B
sum-map f = sum-to ∘′ f ∘′ sum-from

module _ {iℓ sℓ pℓ} {I : Type iℓ} {C : Container sℓ pℓ} {aℓ} {A : Type aℓ} where
    private
        constexp-correct = ConstantExponentiation.correct {I = I} C {X = A}

    open FunEq.Π (Inverse.to constexp-correct) public
        using () renaming (_⟨$⟩_ to constexp-from)

    open FunEq.Π (Inverse.from constexp-correct) public
        using () renaming (_⟨$⟩_ to constexp-to)

constexp-map : ∀{iℓ jℓ sℓ pℓ} {I : Type iℓ} {J : Type jℓ} {C : Container sℓ pℓ}
               {aℓ bℓ} {A : Type aℓ} {B : Type bℓ} →
               ( (I → ⟦ C ⟧ A ) → (J → ⟦ C ⟧ B) ) →
               ⟦ Cc.const[ I ]⟶ C ⟧ A → ⟦ Cc.const[ J ]⟶ C ⟧ B
constexp-map f = constexp-to ∘′ f ∘′ constexp-from
