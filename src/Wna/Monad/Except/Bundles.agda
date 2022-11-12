{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Bundles where

open import Wna.Class.Monad.Handle              using (MonadHandle)
open import Wna.Class.Monad.Raise               using (MonadRaise)
open import Wna.Class.Monad.Trans
open import Wna.Class.RawApplicative            using (RawApplicative; module ApplicativeFT)
open import Wna.Class.RawFunctor                using (Fun; RawFunctor)
open import Wna.Class.RawMonad                  using (RawMonad; module MonadFT; module MkRawMonad)
open import Wna.Monad.Except.Base
open import Wna.Monad.Identity.Bundles  as Id   using ()
open import Wna.Monad.Trans
open import Wna.Primitive

module _ {eℓ} {E : Type eℓ} where

    rawMonadT : RawMonadT (ExceptT E)
    rawMonadT = MkRawMonad.from:pure,>>= pureT _>>=T_

    rawMonad : RawMonad (Except E)
    rawMonad = MkRawMonad.from:pure,>>= pure _>>=_

    rawApplicativeT : RawMonadT-RawApplicative (ExceptT E)
    rawApplicativeT = RawMonad.rawApplicative rawMonadT

    rawApplicative : RawApplicative (Except E)
    rawApplicative = rawApplicativeT ⦃ Id.rawMonad ⦄

    rawFunctorT : RawMonadT-RawFunctor (ExceptT E)
    rawFunctorT = RawMonad.rawFunctor rawMonadT

    rawFunctor : RawFunctor (Except E)
    rawFunctor = rawFunctorT ⦃ Id.rawMonad ⦄

    monadRaise : ∀{M} ⦃ M-monad : RawMonad M ⦄ → MonadRaise E (ExceptT E M)
    monadRaise = record
        { raise    = raiseT
        ; rawMonad = rawMonadT
        }

    monadHandle : ∀{M} ⦃ M-monad : RawMonad M ⦄ → MonadHandle E (ExceptT E M)
    monadHandle = record
        { handle   = handleT
        ; rawMonad = rawMonadT
        }

    monadTrans : MonadTrans (ExceptT E)
    monadTrans = record
        { lift = lift
        }
