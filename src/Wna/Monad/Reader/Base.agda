{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Base where

open import Function.Base               using (const; flip; id; _$_; _∘′_)
open import Wna.Class.RawApplicative    using (IFun; Fun⇒IFun)
open import Wna.Class.RawFunctor        using (Fun)
open import Wna.Class.RawMonad          using (RawIMonad; module IMonadFT)
open import Wna.Monad.Identity          using (Identity)
open import Wna.Monad.Trans             using (MonT)
open import Wna.Primitive

record ReaderIT {rℓ} (R : Type rℓ) {iℓ} {I : Type iℓ} (M : IFun I rℓ) (i j : I) (A : Type rℓ) : Type rℓ where
    no-eta-equality
    pattern
    constructor mkReader
    field
        runReader : R → M i j A

open ReaderIT public

ReaderT : ∀{rℓ} (R : Type rℓ) → MonT rℓ rℓ
ReaderT R M = ReaderIT R (Fun⇒IFun M) _ _

Reader : ∀{rℓ} (R : Type rℓ) → Fun rℓ
Reader R = ReaderT R Identity

module _ {rℓ} {R : Type rℓ} {iℓ} {I : Type iℓ} {M : IFun I rℓ} ⦃ M-imonad : RawIMonad M ⦄ where
    private
        module M = RawIMonad M-imonad

    pure : IMonadFT.pure (ReaderIT R M)
    pure = mkReader ∘′ const ∘′ M.pure

    _>>=_ : IMonadFT._>>=_ (ReaderIT R M)
    _>>=_ (mkReader x) f = mkReader λ r → x r M.>>= flip runReader r ∘′ f

    _<*>_ : IMonadFT._<*>_ (ReaderIT R M)
    (mkReader f) <*> (mkReader x) = mkReader $ λ r → f r M.<*> x r

    lift : ∀{i j} {A : Type rℓ} → M i j A → ReaderIT R M i j A
    lift = mkReader ∘′ const

    ask : ∀{i} → ReaderIT R M i i R
    ask = mkReader M.pure

    local : (R → R) → {A : Type rℓ} → ∀{i j} → ReaderIT R M i j A → ReaderIT R M i j A
    local f (mkReader m) = mkReader (m ∘′ f)
