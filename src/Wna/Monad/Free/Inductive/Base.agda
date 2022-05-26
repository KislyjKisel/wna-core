{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Free.Inductive.Base where

open import Data.Container.Combinator         as Cc   using ()
open import Data.Container.Core               as C    using (Container; ⟦_⟧; _▷_)
open import Data.Container.Relation.Unary.Any         using (any)
open import Data.Empty.Polymorphic                    using (⊥)
open import Data.Product                              using (_,_)
open import Data.Sum.Base                     as ⊎    using (inj₁; inj₂; _⊎_)
open import Data.W                            as W    using (W; sup)
open import Function.Base                             using (const; flip; _∘′_; _$′_)
open import Wna.Class.RawMonad                        using (RawMonad)
open import Wna.Class.Traversable             as Trav using (Traversable)
open import Wna.Data.Container.Conversion     as Cp   using ()
open import Wna.Monad.Free.Container                  using (FreeC)
open import Wna.Primitive

record FreeT {ℓ} (F M : Container ℓ ℓ) (A : Type ℓ) : Type ℓ where
    constructor mkFree
    field
        runFree : W $′ FreeC F M A

open FreeT public
    using (runFree)

Free : ∀{ℓ} (F : Container ℓ ℓ) → Type ℓ → Type ℓ
Free F = FreeT F Cc.id

module _ {ℓ} {F M : Container ℓ ℓ} ⦃ M-monad : RawMonad {aℓ = ℓ} ⟦ M ⟧ ⦄ where
    private
        module M = RawMonad M-monad

    wrap : ∀{A} → ⟦ F ⟧ (FreeT F M A) → FreeT F M A
    wrap (s , p) = mkFree $′ sup $′ Cp.composition-to $′ M.pure $′ (inj₁ s , runFree ∘′ p)

    fold : ⦃ _ : Traversable {ℓ} ⟦ F ⟧ ⦄ {A B : Type ℓ} → (A → ⟦ M ⟧ B) → (⟦ F ⟧ B → ⟦ M ⟧ B) → FreeT F M A → ⟦ M ⟧ B
    fold hpure hfree (mkFree w) = flip W.foldr w (λ t → Cp.composition-from t M.>>= λ where
           (inj₁ fr , pos) → Trav.Instanced.sequenceA (fr , pos) M.>>= hfree
           (inj₂ pr , pos) → hpure pr
        )

    mapMonad : ∀{M'} → (∀{A : Type ℓ} → ⟦ M ⟧ A → ⟦ M' ⟧ A) → ∀{A} → FreeT F M A → FreeT F M' A
    mapMonad {M'} f (mkFree w) = mkFree $′ flip W.foldr w $′
        sup ∘′ Cp.composition-to ∘′ f ∘′ Cp.composition-from

    map : ∀{A B} → (A → B) → FreeT F M A → FreeT F M B
    map f = mkFree ∘′ 
                (W.map $′ C.map (⊎.map₂ f) ▷ 
                    λ{ {_ , mp} (any (p , v)) → any $′ p , aux _ f (mp p) v })
            ∘′ runFree
        where
        aux : ∀{ℓ} {A B C : Type ℓ} (f : A → Type ℓ) (h : B → C) → (x : A ⊎ B) → ⊎.[ f , const ⊥ ]′ (⊎.map₂ h x) → ⊎.[ f , const ⊥ ]′ x
        aux f h (inj₁ x) p = p

    pure : ∀{A} → A → FreeT F M A
    pure x = mkFree $′ sup $′ Cp.composition-to $′ M.pure $′ inj₂ x , λ ()

    join : ∀{A} → FreeT F M (FreeT F M A) → FreeT F M A
    join {A} = mkFree ∘′
            (W.foldr $′
                sup ∘′ Cp.composition-to ∘′
                M.join ∘′ M.map (Cp.composition-from ∘′ aux) ∘′
                Cp.composition-from) ∘′
            runFree
        where
        aux : ⟦ F Cc.⊎ Cc.const (FreeT F M A) ⟧ (W $′ FreeC F M A) → ⟦ FreeC F M A ⟧ (W $′ FreeC F M A)
        aux (inj₁ a , p)                = Cp.composition-to $′ M.pure $′ inj₁ a , p
        aux (inj₂ (mkFree (sup w)) , p) = w

    _>>=_ : ∀{A B} → FreeT F M A → (A → FreeT F M B) → FreeT F M B
    _>>=_ x f = join $′ map f x
