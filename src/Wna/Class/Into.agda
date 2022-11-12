{-# OPTIONS --without-K --safe #-}

module Wna.Class.Into where

open import Data.Sum.Base                                   using (inj₁; inj₂)
open import Data.Sum.Effectful.Left                         using (Sumₗ)
open import Data.Sum.Effectful.Left.Transformer as SumₗT    using (SumₗT; mkSumₗT)
open import Effect.Monad                                    using (RawMonad; RawMonadTd)
open import Function.Base                                   using (_$′_; _∘′_)
open import Function.Identity.Effectful         as Identity using (Identity)
open import Level                               as ℓ        using (Level; 0ℓ)
open import Relation.Nullary.Negation                       using (¬_)
open import Wna.Class.Decide                                using (DecideM; Decide; decideM; yes; no)
open import Wna.Relation.Nullary.Decidable                  using (to⊎)

private
    variable
        aℓ bℓ cℓ : Level
        A B : Set aℓ
        M : Set aℓ → Set aℓ


record IntoM cℓ (A : Set aℓ) (M : Set bℓ → Set bℓ) (B : Set bℓ) : Set (ℓ.suc cℓ ℓ.⊔ aℓ ℓ.⊔ bℓ) where
    field
        Constraint : A → Set cℓ
        intoM : (x : A) → Constraint x → M B

open IntoM public
    using (Constraint)

open IntoM ⦃...⦄ public
    using (intoM)

intoM? : ⦃ RawMonad M ⦄ → ⦃ IntoM[⋯] : IntoM cℓ A M B ⦄ → (x : A) → ⦃ DecideM M (Constraint IntoM[⋯] x) ⦄ → SumₗT (¬ Constraint IntoM[⋯] x) cℓ M B
intoM? {cℓ = cℓ} ⦃ M[M] ⦄ x = mkSumₗT $′ decideM _ M[M].>>= λ where
        (yes c) → inj₂ M[M].<$> intoM x c
        (no ¬c) → M[M].pure $′ inj₁ ¬c
    where
    module M[M] = RawMonad M[M]

intoM! : ⦃ IntoM[⋯] : IntoM cℓ A M B ⦄ → (x : A) → ⦃ Constraint IntoM[⋯] x ⦄ → M B
intoM! x ⦃ c ⦄ = intoM x c

Into : ∀ cℓ → Set aℓ → Set bℓ → Set (ℓ.suc cℓ ℓ.⊔ aℓ ℓ.⊔ bℓ)
Into cℓ A B = IntoM cℓ A Identity B

into : ⦃ Into[⋯] : Into cℓ A B ⦄ → (x : A) → Constraint Into[⋯] x → B
into = intoM

into? : ⦃ Into[⋯] : Into cℓ A B ⦄ → (x : A) → ⦃ Decide (Constraint Into[⋯] x) ⦄ → Sumₗ (¬ Constraint Into[⋯] x) cℓ B
into? x = SumₗT.runSumₗT $′ intoM? ⦃ Identity.monad ⦄ x

into! : ⦃ Into[⋯] : Into cℓ A B ⦄ → (x : A) → ⦃ Constraint Into[⋯] x ⦄ → B
into! = intoM!
