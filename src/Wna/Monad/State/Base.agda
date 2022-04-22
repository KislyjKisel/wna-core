{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Base where

open import Data.Product using (_×_)
open import Wna.Class.Monad.Trans using (MonT; MonIT; MonTI)
open import Wna.Class.RawApplicative using (IFun)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Monad.Identity using (Identity)

record StateTI {ℓ} (M : Fun ℓ) (i j : Type ℓ) (A : Type ℓ) : Type ℓ where
    inductive
    no-eta-equality
    pattern
    constructor mkState
    field
        runState : i → M (A × j) 

open StateTI public

IState : ∀{ℓ} → IFun (Set ℓ) ℓ
IState = StateTI Identity

StateIT : ∀{ℓ} → Type ℓ → MonIT ℓ ℓ
StateIT S M i j = StateTI (M i j) S S

StateT : ∀{ℓ} → Type ℓ → MonT ℓ ℓ
StateT S M = StateTI M S S

State : ∀{ℓ} → Type ℓ → Fun ℓ
State S = StateT S Identity
