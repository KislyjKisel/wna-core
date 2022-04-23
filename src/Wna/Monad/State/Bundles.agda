{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Bundles where

open import Data.Product using (_,′_; _,_)
open import Wna.Monad.Trans
open import Wna.Class.RawApplicative using (IFun; module MkRawIApplicative)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad using (RawIMonad; RawMonad; module IMonadFT; module MkRawIMonad)
open import Wna.Monad.Identity using () renaming (rawMonad to id-rawMonad)
open import Wna.Monad.State.Base
open import Wna.Class.Monad.Trans using (Trans)
open import Wna.Class.Monad.State as CS using ()
open import Wna.Primitive

rawMonadTI : ∀{ℓ} → RawMonadTI (StateTI {ℓ}) 
rawMonadTI {ℓ = ℓ} {F = M'} ⦃ M ⦄ = record
    { rawIApplicative = MkRawIApplicative.from:pure,<*> ipure (MkRawIMonad.pure,>>=⇒<*> {F = StateTI M'} ipure _i>>=_)
    ; _>>=_           = _i>>=_
    ; join            = MkRawIMonad.>>=⇒join {F = StateTI M'} _i>>=_
    }

rawIMonad : ∀{ℓ} → RawIMonad (IState {ℓ = ℓ})
rawIMonad = rawMonadTI ⦃ id-rawMonad ⦄

rawMonadIT : ∀{ℓ} {S : Type ℓ} → RawMonadIT (StateIT S)
rawMonadIT {ℓ = ℓ} {S = S} {I = I} {F = M} ⦃ M-imonad ⦄ = record
    { rawIApplicative = MkRawIApplicative.from:pure,<*> pure (MkRawIMonad.pure,>>=⇒<*> {F = StateIT S M} pure _>>=_)
    ; _>>=_           = _>>=_
    ; join            = MkRawIMonad.>>=⇒join {F = StateIT S M} _>>=_
    }
    where
    module M = RawIMonad M-imonad

rawMonadT : ∀{ℓ} {S : Type ℓ} → RawMonadT (StateT S)
rawMonadT ⦃ M ⦄ = rawMonadIT ⦃ M ⦄

module _ {ℓ} where
    open RawIMonad (rawIMonad {ℓ = ℓ}) public using
        ( rawMonad
        ; rawApplicative; rawIApplicative
        ; rawFunctor
        )

trans : ∀{sℓ} {S : Type sℓ} → Trans (StateT S)
trans = record
    { lift = lift
    }


istate : ∀{ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ → CS.IState (StateTI M) ⦃ rawMonadTI ⦃ M-monad ⦄ ⦄
istate = record
    { iget = iget
    ; iput = iput
    }

state : ∀{ℓ} {I : Type ℓ} {M : IFun I ℓ} ⦃ M-monad : RawIMonad M ⦄ {S : Type ℓ} {i : I} →
        CS.State (StateIT S M i i) ⦃ RawIMonad.rawMonad (rawMonadIT {S = S} ⦃ M-monad ⦄) {i = i} ⦄
state {S = S} = record
    { S   = S
    ; get = get
    ; put = put
    }
