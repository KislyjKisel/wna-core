{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Bundles where

open import Wna.Class.Monad.Ask                 using (MonadAsk)
open import Wna.Class.Monad.Local               using (MonadLocal)
open import Wna.Class.Monad.Trans               using (MonadTrans)
open import Wna.Class.RawApplicative            using (IFun; module MkRawIApplicative)
open import Wna.Class.RawMonad                  using (RawIMonad; RawMonad; module MkRawIMonad)
open import Wna.Monad.Identity.Bundles  as Id   using ()
open import Wna.Monad.Reader.Base
open import Wna.Monad.Trans
open import Wna.Primitive

module _ {rℓ} {R : Type rℓ} where

    rawMonadIT : RawMonadIT (ReaderIT R)
    rawMonadIT {F = M} ⦃ M-imonad ⦄ = record
        { rawIApplicative = MkRawIApplicative.from:pure,<*> pure _<*>_
        ; _>>=_           = _>>=_
        ; join            = MkRawIMonad.>>=⇒join {F = ReaderIT R M} _>>=_
        }

    rawMonadT : RawMonadT (ReaderT R)
    rawMonadT = rawMonadIT

    rawMonad : RawMonad (Reader R)
    rawMonad = rawMonadT ⦃ Id.rawMonad ⦄

    rawApplicative : RawMonadT-RawApplicative (ReaderT R)
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : RawMonadT-RawFunctor (ReaderT R)
    rawFunctor = RawMonad.rawFunctor rawMonadT

    monadAsk : ∀{iℓ} {I : Type iℓ} {i : I} {M : IFun I rℓ} ⦃ M-monad : RawIMonad M ⦄ → MonadAsk R (ReaderIT R M i i)
    monadAsk = record
        { ask      = ask
        ; rawMonad = RawIMonad.rawMonad rawMonadIT
        }

    monadLocal : ∀{iℓ} {I : Type iℓ} {i : I} {M : IFun I rℓ} ⦃ M-monad : RawIMonad M ⦄ → MonadLocal R (ReaderIT R M i i)
    monadLocal = record
        { local    = λ f → local f
        ; M-ask    = monadAsk
        ; rawMonad = RawIMonad.rawMonad rawMonadIT
        }

    monadTrans : MonadTrans (ReaderT R)
    monadTrans = record
        { lift = lift
        }
