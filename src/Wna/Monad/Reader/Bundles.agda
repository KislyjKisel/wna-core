{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Bundles where

open import Function.Base                       using (_$_)
open import Wna.Class.Monad.Ask                 using (Ask)
open import Wna.Class.Monad.Local               using (Local)
open import Wna.Class.Monad.Trans               using (Trans)
open import Wna.Class.RawApplicative            using (IFun; module MkRawIApplicative)
open import Wna.Class.RawMonad                  using (RawIMonad; RawMonad; module MkRawIMonad)
open import Wna.Monad.Identity.Bundles  as Id   using ()
open import Wna.Monad.Reader.Base       as Re   hiding (ask; local)
open import Wna.Monad.Trans                     using (RawMonadIT; RawMonadT)
open import Wna.Primitive

module _ {rℓ} {R : Type rℓ} where

    rawMonadIT : RawMonadIT (ReaderIT R)
    rawMonadIT {F = M} ⦃ M-imonad ⦄ = record
        { rawIApplicative = MkRawIApplicative.from:pure,<*> pure _<*>_
        ; _>>=_           = _>>=_
        ; join            = MkRawIMonad.>>=⇒join {F = ReaderIT R M} _>>=_
        }

    rawMonadT : RawMonadT (ReaderT R)
    rawMonadT ⦃ M-monad ⦄ = rawMonadIT ⦃ M-monad ⦄

    rawMonad : RawMonad (Reader R)
    rawMonad = rawMonadT ⦃ Id.rawMonad ⦄

    open RawMonad rawMonad public using
        ( rawApplicative
        ; rawFunctor
        )

    ask : ∀{iℓ} {I : Type iℓ} {i : I} {M : IFun I rℓ} ⦃ M-monad : RawIMonad M ⦄ → Ask (ReaderIT R M i i) ⦃ RawIMonad.rawMonad $ rawMonadIT ⦃ M-monad ⦄ ⦄
    ask ⦃ M-monad ⦄ = record
        { E   = R
        ; ask = Re.ask
        }

    local : ∀{iℓ} {I : Type iℓ} {i : I} {M : IFun I rℓ} ⦃ M-monad : RawIMonad M ⦄ → Local (ReaderIT R M i i) ⦃ RawIMonad.rawMonad $ rawMonadIT ⦃ M-monad ⦄ ⦄
    local {I = I} {i = i} ⦃ M-monad ⦄ = record
        { local = λ f → Re.local {I = I} f
        ; M-ask = ask
        }

    trans : Trans (ReaderT R)
    trans = record
        { lift = lift
        }
