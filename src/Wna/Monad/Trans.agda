{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Trans where

open import Data.Unit                                   using (⊤)
open import Wna.Class.RawApplicative                    using (IFun; RawIApplicative; RawApplicative)
open import Wna.Class.RawFunctor                        using (Fun; RawFunctor)
open import Wna.Class.RawMonad                          using (RawMonad; RawIMonad)
open import Wna.Primitive

-- Transformer itself

MonT : ∀ aℓ bℓ → Type (ℓ↑ (aℓ ℓ⊔ bℓ))
MonT aℓ bℓ = Fun aℓ → Fun bℓ

MonTI : (aℓ bℓ : Level) → ∀{iℓ} (I : Type iℓ) → Type (ℓ↑ aℓ ℓ⊔ ℓ↑ bℓ ℓ⊔ iℓ)
MonTI aℓ bℓ I = Fun aℓ → IFun I bℓ

MonIT : (aℓ bℓ : Level) → Typeω
MonIT aℓ bℓ = ∀{iℓ} {I : Type iℓ} → IFun I aℓ → IFun I bℓ

-- Raw (operation) transformers

RawMonadT : ∀{aℓ bℓ} (T : MonT aℓ bℓ) → Type _
RawMonadT {aℓ = aℓ} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawMonad (T F)

RawMonadTI : ∀{aℓ bℓ iℓ} {I : Type iℓ} (T : MonTI aℓ bℓ I) → Type (ℓ↑ aℓ ℓ⊔ ℓ↑ bℓ ℓ⊔ iℓ)
RawMonadTI {aℓ = aℓ} {I = I} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawIMonad (T F)

RawMonadIT : ∀{aℓ bℓ} (T : MonIT aℓ bℓ) → Typeω
RawMonadIT {aℓ} {bℓ} T = ∀{iℓ} {I : Type iℓ} {F : IFun I aℓ} → ⦃ _ : RawIMonad F ⦄ → RawIMonad (T F)

RawMonadT-RawApplicative : ∀{aℓ bℓ} (T : MonT aℓ bℓ) → Type _
RawMonadT-RawApplicative {aℓ = aℓ} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawApplicative (T F)

RawMonadTI-RawApplicative : ∀{aℓ bℓ iℓ} {I : Type iℓ} (T : MonTI aℓ bℓ I) → Type (ℓ↑ aℓ ℓ⊔ ℓ↑ bℓ ℓ⊔ iℓ)
RawMonadTI-RawApplicative {aℓ = aℓ} {I = I} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawIApplicative (T F)

RawMonadIT-RawApplicative : ∀{aℓ bℓ} (T : MonIT aℓ bℓ) → Typeω
RawMonadIT-RawApplicative {aℓ} {bℓ} T = ∀{iℓ} {I : Type iℓ} {F : IFun I aℓ} → ⦃ _ : RawIMonad F ⦄ → RawIApplicative (T F)

RawMonadT-RawFunctor : ∀{aℓ bℓ} (T : MonT aℓ bℓ) → Type _
RawMonadT-RawFunctor {aℓ = aℓ} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawFunctor (T F)

RawMonadTI-RawFunctor : ∀{aℓ bℓ iℓ} {I : Type iℓ} (T : MonTI aℓ bℓ I) → Type (ℓ↑ aℓ ℓ⊔ ℓ↑ bℓ ℓ⊔ iℓ)
RawMonadTI-RawFunctor {aℓ = aℓ} {I = I} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → ∀{i} → RawFunctor (T F i i)

RawMonadIT-RawFunctor : ∀{aℓ bℓ} (T : MonIT aℓ bℓ) → Typeω
RawMonadIT-RawFunctor {aℓ} {bℓ} T = ∀{iℓ} {I : Type iℓ} {F : IFun I aℓ} → ⦃ _ : RawIMonad F ⦄ → ∀{i} → RawFunctor (T F i i)

--

MonT⇒MonIT : ∀{aℓ bℓ} → MonT aℓ bℓ → MonIT aℓ bℓ
MonT⇒MonIT T IM i j = T (IM i j)
