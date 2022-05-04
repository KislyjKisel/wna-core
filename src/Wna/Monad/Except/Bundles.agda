{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Bundles where

open import Wna.Class.Monad.Handle              using (Handle)
open import Wna.Class.Monad.Raise               using (Raise)
open import Wna.Class.Monad.Trans
open import Wna.Class.RawApplicative            using (module ApplicativeFT)
open import Wna.Class.RawFunctor                using (Fun)
open import Wna.Class.RawMonad                  using (RawMonad; module MonadFT; module MkRawMonad)
open import Wna.Monad.Except.Base       as Ex   hiding (raise; handle)
open import Wna.Monad.Identity.Bundles  as Id   using ()
open import Wna.Monad.Trans
open import Wna.Primitive

module _ {eℓ} {E : Type eℓ} where
 
    rawMonadT : RawMonadT (ExceptT E)
    rawMonadT = record
        { rawIApplicative = MkRawMonad.pure,>>=⇒rawApplicative pure _>>=_
        ; _>>=_           = _>>=_
        ; join            = MkRawMonad.>>=⇒join _>>=_
        }

    rawMonad : RawMonad (Except E)
    rawMonad = rawMonadT ⦃ Id.rawMonad ⦄

    rawApplicative : RawMonadT-RawApplicative (ExceptT E)
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : RawMonadT-RawFunctor (ExceptT E)
    rawFunctor = RawMonad.rawFunctor rawMonadT

    raise : ∀{M} ⦃ M-monad : RawMonad M ⦄ → Raise (ExceptT E M)
    raise = record
        { E        = _
        ; raise    = Ex.raise
        ; rawMonad = rawMonadT
        }

    handle : ∀{M} ⦃ M-monad : RawMonad M ⦄ → Handle (ExceptT E M)
    handle = record
        { E        = _
        ; handle   = Ex.handle
        ; rawMonad = rawMonadT
        }

    trans : Trans (ExceptT E)
    trans = record
        { lift = Ex.lift
        }
