{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Bundles where

open import Wna.Class.Monad.State            using (IMonadState; MonadState)
open import Wna.Class.Monad.Trans            using (MonadTrans)
open import Wna.Class.RawApplicative         using (RawIApplicative; RawApplicative; IFun; module MkRawIApplicative)
open import Wna.Class.RawFunctor             using (Fun; RawFunctor)
open import Wna.Class.RawMonad
open import Wna.Monad.Identity.Bundles as Id using ()
open import Wna.Monad.State.Base
open import Wna.Monad.Trans
open import Wna.Primitive

rawMonadTI : ∀{ℓ} → RawMonadTI (StateTI {ℓ})
rawMonadTI = MkRawIMonad.from:pure,>>= pureTI _>>=TI_

rawMonadI : ∀{ℓ} → RawIMonad (StateI {ℓ = ℓ})
rawMonadI = rawMonadTI ⦃ Id.rawMonad ⦄

rawMonadT : ∀{ℓ} {S : Type ℓ} → RawMonadT (StateT S)
rawMonadT = MkRawMonad.from:pure,>>= pureTI _>>=TI_

module _ {ℓ} where
    open RawIMonad (rawMonadI {ℓ = ℓ}) public
        using (rawMonad)

module _ {ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ where

    rawApplicativeI : RawIApplicative (StateTI M)
    rawApplicativeI = RawIMonad.rawIApplicative rawMonadTI

    rawApplicative : ∀{S : Type ℓ} → RawApplicative (StateT S M)
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : ∀{i} → RawFunctor (StateTI M i i)
    rawFunctor = RawMonad.rawFunctor rawMonadT

monadTrans : ∀{sℓ} {S : Type sℓ} → MonadTrans (StateT S)
monadTrans = record
    { lift = lift
    }


statei : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ → IMonadState (StateTI M)
statei = record
    { iget      = getTI
    ; iput      = putTI
    ; rawIMonad = rawMonadTI
    }

state : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ {S : Type ℓ} → MonadState S (StateT S M)
state = record
    { get      = getTI
    ; put      = putTI
    ; rawMonad = rawMonadT
    }
