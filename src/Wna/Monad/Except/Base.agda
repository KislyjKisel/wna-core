{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Base where

open import Data.Sum.Base           using (inj₁; inj₂; _⊎_)
open import Function.Base           using (_$_; _∘′_)
open import Wna.Class.RawFunctor    using (Fun)
open import Wna.Class.RawMonad      using (RawMonad; module MonadFT)
open import Wna.Monad.Identity.Base using (Identity)
open import Wna.Monad.Trans         using (MonT)
open import Wna.Primitive

record ExceptT {ℓ} (E : Type ℓ) (M : Fun ℓ) (A : Type ℓ) : Type ℓ where
    no-eta-equality
    pattern
    constructor mkExcept
    field
        runExcept : M (E ⊎ A)

open ExceptT public

Except : ∀{ℓ} (E : Type ℓ) → Fun ℓ
Except E = ExceptT E Identity

pure : ∀{ℓ} {E : Type ℓ} {M : Fun ℓ} ⦃ _ : RawMonad M ⦄ → MonadFT.pure (ExceptT E M)
pure ⦃ M-monad ⦄ x = mkExcept $ RawMonad.pure M-monad (inj₂ x)

_>>=_ : ∀{ℓ} {E : Type ℓ} {M : Fun ℓ} ⦃ _ : RawMonad M ⦄ → MonadFT._>>=_ (ExceptT E M)
_>>=_ ⦃ M-monad ⦄ (mkExcept mx) f = mkExcept $ mx M.>>= λ where
        (inj₁ e) → M.pure (inj₁ e)
        (inj₂ x) → runExcept $ f x
    where module M = RawMonad M-monad

lift : ∀{ℓ} {E : Type ℓ} {M} ⦃ M-monad : RawMonad M ⦄ {A : Type ℓ} → M A → ExceptT E M A
lift ⦃ M-monad ⦄ = mkExcept ∘′ RawMonad.fmap M-monad inj₂

raise : ∀{ℓ} {E : Type ℓ} {M} ⦃ M-monad : RawMonad M ⦄ → E → ∀{A : Type ℓ} → ExceptT E M A
raise ⦃ M-monad ⦄ e = mkExcept (RawMonad.pure M-monad (inj₁ e))

handle : ∀{ℓ} {E A : Type ℓ} {M} ⦃ M-monad : RawMonad M ⦄ → ExceptT E M A → (E → ExceptT E M A) → ExceptT E M A
handle ⦃ M-monad ⦄ (mkExcept m) h = mkExcept (m M.>>= λ where
        (inj₁ e) → runExcept (h e)
        (inj₂ x) → M.pure (inj₂ x)
    )
    where module M = RawMonad M-monad
