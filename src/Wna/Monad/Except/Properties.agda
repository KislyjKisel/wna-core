{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Properties where

import Wna.Monad.Identity.Properties as Id
open import Data.Sum using (inj₁; inj₂)
open import Function using (_$_)
open import Wna.Class.Monad.Trans
open import Wna.Class.RawApplicative using (module ApplicativeFT)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad using (RawMonad; module MonadFT; module MkRawMonad)
open import Wna.Monad.Except.Base

rawMonadT : ∀{eℓ} {E : Type eℓ} → RawMonadT (ExceptT E)
rawMonadT {eℓ = eℓ} {E = E} {F = M'} {{M}} = record
    { rawIApplicative = MkRawMonad.pure,>>=⇒rawApplicative pure bind
    ; _>>=_           = bind
    ; join            = MkRawMonad.>>=⇒join bind }
    where
    module M = RawMonad M

    TM : Fun eℓ
    TM = ExceptT E M'

    pure : ApplicativeFT.pure TM
    pure x = mkExcept $ M.pure (inj₂ x)

    bind : MonadFT._>>=_ TM
    bind (mkExcept mx) f = mkExcept $ mx M.>>= λ{ (inj₁ e) → M.pure (inj₁ e)
                                                ; (inj₂ x) → runExcept $ f x
                                                }

rawMonad : ∀{eℓ} {E : Type eℓ} → RawMonad (Except E)
rawMonad = rawMonadT ⦃ Id.rawMonad ⦄

module _ {eℓ} {E : Type eℓ} where
    open RawMonad (rawMonad {eℓ = eℓ} {E = E}) public
        using (rawApplicative; rawFunctor)
