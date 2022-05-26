{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Base where

open import Data.Sum.Base            using (inj₁; inj₂; _⊎_)
open import Function.Base            using (_$′_; _∘′_)
open import Wna.Class.RawFunctor     using (Fun)
open import Wna.Class.RawMonad       using (RawMonad; module MonadFT)
open import Wna.Monad.Identity as Id using (Identity)
open import Wna.Monad.Trans          using (MonT)
open import Wna.Primitive

record ExceptT {ℓ} (E : Type ℓ) (M : Fun ℓ) (A : Type ℓ) : Type ℓ where
    no-eta-equality
    pattern
    constructor makeT
    field
        runT : M (E ⊎ A)

open ExceptT public

Except : ∀{ℓ} (E : Type ℓ) → Fun ℓ
Except E = ExceptT E Identity

module _ {ℓ} {E : Type ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ where 
    private
        module M = RawMonad M-monad

    pureT : MonadFT.pure (ExceptT E M)
    pureT x = makeT $′ M.pure $′ inj₂ x

    _>>=T_ : MonadFT._>>=_ (ExceptT E M)
    _>>=T_ (makeT mx) f = makeT $′ mx M.>>= λ where
            (inj₁ e) → M.pure (inj₁ e)
            (inj₂ x) → runT $′ f x

    lift : {A : Type ℓ} → M A → ExceptT E M A
    lift = makeT ∘′ M.map inj₂

    raiseT : E → ∀{A : Type ℓ} → ExceptT E M A
    raiseT e = makeT $′ M.pure $′ inj₁ e

    handleT : ∀{A : Type ℓ} → ExceptT E M A → (E → ExceptT E M A) → ExceptT E M A
    handleT (makeT m) h = makeT (m M.>>= λ where
            (inj₁ e) → runT (h e)
            (inj₂ x) → M.pure (inj₂ x)
        )

module _ {ℓ} {E : Type ℓ} where

    make : ∀{A} → E ⊎ A → Except E A
    make = makeT ∘′ Id.mkIdentity

    run : ∀{A} → Except E A → E ⊎ A
    run = Id.runIdentity ∘′ runT

    pure : MonadFT.pure (Except E)
    pure = pureT ⦃ Id.rawMonad ⦄

    _>>=_ : MonadFT._>>=_ (Except E)
    _>>=_ = _>>=T_ ⦃ Id.rawMonad ⦄

    raise : E → ∀{A} → Except E A
    raise = raiseT ⦃ Id.rawMonad ⦄

    handle : ∀{A} → Except E A → (E → Except E A) → Except E A
    handle = handleT ⦃ Id.rawMonad ⦄
