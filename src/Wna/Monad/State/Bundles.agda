{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Bundles where

open import Wna.Class.Monad.State      as CS using ()
open import Wna.Class.Monad.Trans            using (Trans)
open import Wna.Class.RawApplicative         using (IFun; module MkRawIApplicative)
open import Wna.Class.RawFunctor             using (Fun)
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

open import Wna.Class.RawApplicative using (RawIApplicative; RawApplicative)
open import Wna.Class.RawFunctor using (RawFunctor)

module _ {ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ where

    rawIApplicative : RawIApplicative (StateTI M)
    rawIApplicative = RawIMonad.rawIApplicative rawMonadTI

    rawApplicative : ∀{S : Type ℓ} → RawApplicative (StateT S M)
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : ∀{i} → RawFunctor (StateTI M i i)
    rawFunctor = RawMonad.rawFunctor rawMonadT

trans : ∀{sℓ} {S : Type sℓ} → Trans (StateT S)
trans = record
    { lift = lift
    }


istate : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ → CS.IState (StateTI M) ⦃ rawMonadTI ⦃ M-monad ⦄ ⦄
istate = record
    { iget = iget
    ; iput = iput
    }

state : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ {S : Type ℓ} →
        CS.State (StateT S M) ⦃ rawMonadT ⦃ M-monad ⦄ ⦄
state ⦃ M-monad ⦄ {S = S} = record
    { S   = S
    ; get = iget
    ; put = iput
    }
