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
rawMonadTI = MkRawIMonad.from:pure,>>= pure _>>=_

rawIMonad : ∀{ℓ} → RawIMonad (IState {ℓ = ℓ})
rawIMonad = rawMonadTI ⦃ Id.rawMonad ⦄

rawMonadT : ∀{ℓ} {S : Type ℓ} → RawMonadT (StateT S)
rawMonadT = MkRawMonad.from:pure,>>= pure _>>=_

module _ {ℓ} where
    open RawIMonad (rawIMonad {ℓ = ℓ}) public
        using (rawMonad)

module _ {ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ where

    rawIApplicative : RawIApplicative (StateTI M)
    rawIApplicative = RawIMonad.rawIApplicative rawMonadTI

    rawApplicative : ∀{S : Type ℓ} → RawApplicative (StateT S M)
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : ∀{i} → RawFunctor (StateTI M i i)
    rawFunctor = RawMonad.rawFunctor rawMonadT

monadTrans : ∀{sℓ} {S : Type sℓ} → MonadTrans (StateT S)
monadTrans = record
    { lift = lift
    }


istate : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ → IMonadState (StateTI M)
istate = record
    { iget      = iget
    ; iput      = iput
    ; rawIMonad = rawMonadTI
    }

state : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ {S : Type ℓ} → MonadState S (StateT S M)
state = record
    { get      = iget
    ; put      = iput
    ; rawMonad = rawMonadT
    }
