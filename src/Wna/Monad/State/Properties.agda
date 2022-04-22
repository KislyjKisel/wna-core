{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Properties where

open import Data.Product using (_,′_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Wna.Class.Monad using (Monad; IMonad)
open import Wna.Class.Monad.Trans
open import Wna.Class.RawApplicative using (IFun; module MkRawIApplicative)
open import Wna.Class.RawMonad using (module IMonadFT; module MkRawIMonad)
open import Wna.Class.RawMonad using (RawMonad; RawIMonad)
open import Wna.Monad.Identity using () renaming (rawMonad to id-rawMonad)
open import Wna.Monad.State.Base

rawMonadTI : ∀{ℓ} → RawMonadTI (StateTI {ℓ}) 
rawMonadTI {ℓ = ℓ} {F = M'} ⦃ M ⦄ = record
    { rawIApplicative = MkRawIApplicative.from:pure,<*> pure (MkRawIMonad.pure,>>=⇒<*> {F = StateTI M'} pure bind)
    ; _>>=_           = bind
    ; join            = MkRawIMonad.>>=⇒join {F = StateTI M'} bind
    }
    where
    module M = RawMonad M
    pure : IMonadFT.pure (StateTI {ℓ = ℓ} M')
    pure = λ x → mkState (λ s → M.pure (x ,′ s))

    bind : IMonadFT._>>=_ (StateTI {ℓ = ℓ} M')
    bind = λ (mkState m) f → mkState λ i → m i M.>>= λ (a , j) → runState (f a) j


rawIMonad : ∀{ℓ} → RawIMonad (IState {ℓ = ℓ})
rawIMonad = rawMonadTI ⦃ id-rawMonad ⦄

rawMonadIT : ∀{ℓ} {S : Type ℓ} → RawMonadIT (StateIT S)
rawMonadIT {ℓ = ℓ} {S = S} {I = I} {F = M'} ⦃ M ⦄ = record
    { rawIApplicative = MkRawIApplicative.from:pure,<*> pure (MkRawIMonad.pure,>>=⇒<*> {F = SM'} pure bind)
    ; _>>=_           = bind
    ; join            = MkRawIMonad.>>=⇒join {F = SM'} bind
    }
    where
    module M = RawIMonad M
    
    SM' : IFun I ℓ
    SM' = StateIT S M'

    pure : IMonadFT.pure SM'
    pure = λ x → mkState (λ s → M.pure (x ,′ s))

    bind : IMonadFT._>>=_ SM'
    bind = λ (mkState m) f → mkState (λ i → m i M.>>= λ (a , j) → runState (f a) j)

rawMonadT : ∀{ℓ} {S : Type ℓ} → RawMonadT (StateT S)
rawMonadT ⦃ M ⦄ = rawMonadIT ⦃ M ⦄

module _ {ℓ} where
    open RawIMonad (rawIMonad {ℓ = ℓ}) public using
        ( rawMonad
        ; rawApplicative; rawIApplicative
        ; rawFunctor
        )
