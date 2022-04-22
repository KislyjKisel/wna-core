{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Trans where

open import Data.Unit                                   using (⊤)
open import Wna.Class.RawApplicative                    using (IFun)
open import Wna.Class.RawApplicative.LevelPolymorphic   using (IFun′)
open import Wna.Class.RawFunctor                        using (Fun)
open import Wna.Class.RawFunctor.LevelPolymorphic       using (Fun′)
open import Wna.Class.RawMonad                          using (RawMonad; RawIMonad)
open import Wna.Class.RawMonad.LevelPolymorphic         using (RawMonad′; RawIMonad′)
open import Wna.Primitive

-- -- Transformer itself

MonT : ∀ aℓ bℓ → Type (ℓ↑ (aℓ ℓ⊔ bℓ))
MonT aℓ bℓ = Fun aℓ → Fun bℓ

MonTI : (aℓ bℓ : Level) → ∀{iℓ} (I : Type iℓ) → Type (ℓ↑ aℓ ℓ⊔ ℓ↑ bℓ ℓ⊔ iℓ)
MonTI aℓ bℓ I = Fun aℓ → IFun I bℓ

MonIT : (aℓ bℓ : Level) → Typeω
MonIT aℓ bℓ = ∀{iℓ} {I : Type iℓ} → IFun I aℓ → IFun I bℓ

-- Level polymorphic

MonT′ : Typeω
MonT′ = Fun′ → Fun′

MonTI′ : ∀{i} (I : Type i) → Typeω
MonTI′ I = Fun′ → IFun′ I

MonIT′ : Typeω
MonIT′ = ∀{iℓ} {I : Type iℓ} → IFun′ I → IFun′ I

-- -- Raw (operation) transformers
-- note: src monad must be instance argument to make these available to instance search (?)

RawMonadT : ∀{aℓ bℓ} (T : MonT aℓ bℓ) → Type _
RawMonadT {aℓ = aℓ} T =  {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawMonad (T F)

RawMonadTI : ∀{aℓ bℓ iℓ} {I : Type iℓ} (T : MonTI aℓ bℓ I) → Type (ℓ↑ aℓ ℓ⊔ ℓ↑ bℓ ℓ⊔ iℓ)
RawMonadTI {aℓ = aℓ} {I = I} T = {F : Fun aℓ} → ⦃ _ : RawMonad F ⦄ → RawIMonad (T F)

RawMonadIT : ∀{aℓ bℓ} (T : MonIT aℓ bℓ) → Typeω
RawMonadIT {aℓ} {bℓ} T = ∀{iℓ} {I : Type iℓ} {F : IFun I aℓ} → ⦃ _ : RawIMonad F ⦄ → RawIMonad (T F)

-- Level polymorphic

RawMonadT′ :  (T : MonT′) → Typeω
RawMonadT′ T = {F : Fun′} → ⦃ _ : RawMonad′ F ⦄ → RawMonad′ (T F)

RawMonadTI′ : ∀{iℓ} {I : Type iℓ} (T : MonTI′ I) → Typeω
RawMonadTI′ {I = I} T = {F : Fun′} → ⦃ _ : RawMonad′ F ⦄ → RawIMonad′ (T F)

RawMonadIT′ : ∀(T : MonIT′) → Typeω
RawMonadIT′ T = ∀{iℓ} {I : Type iℓ} {F : IFun′ I} → ⦃ _ : RawIMonad′ F ⦄ → RawIMonad′ (T F)

-- --

MonT⇒MonIT : ∀{aℓ bℓ} → MonT aℓ bℓ → MonIT aℓ bℓ
MonT⇒MonIT T IM i j = T (IM i j)

MonT′⇒MonIT′ : MonT′ → MonIT′
MonT′⇒MonIT′ T′ IM′ i j = T′ (IM′ i j)

-- --
