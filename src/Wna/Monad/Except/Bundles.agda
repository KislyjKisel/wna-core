{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Bundles where

open import Wna.Class.Monad.Handle              using (MonadHandle)
open import Wna.Class.Monad.Raise               using (MonadRaise)
open import Wna.Class.Monad.Trans
open import Wna.Class.RawApplicative            using (module ApplicativeFT)
open import Wna.Class.RawFunctor                using (Fun)
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

    rawApplicative : RawMonadT-RawApplicative (ExceptT E)
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : RawMonadT-RawFunctor (ExceptT E)
    rawFunctor = RawMonad.rawFunctor rawMonadT

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
