{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Instances where

open import Data.Product using (_,_)
open import Function using (const; _$_)
open import Wna.Class.RawApplicative using (IFun)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad using (RawMonad; RawIMonad)
open import Wna.Class.Monad.State using (IState⇒State) renaming (State to ClassState; IState to ClassIState)
open import Wna.Class.Monad.Trans
open import Wna.Monad.State.Base
open import Wna.Monad.State.Properties

module _ {ℓ} where

    StateTI<:IState : ∀{M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ → ClassIState (StateTI M) ⦃ rawMonadTI ⦃ M-monad ⦄ ⦄
    StateTI<:IState ⦃ M-monad ⦄ = record
        { iget = mkState λ x → RawMonad.pure M-monad (x , x)
        ; iput = λ x → mkState $ const $ RawMonad.pure M-monad (_ , x)
        }

    StateIT<:State : ∀{I : Type ℓ}{M : IFun I ℓ} ⦃ M-monad : RawIMonad M ⦄ {S : Type ℓ} {i : I} →
                     ClassState (StateIT S M i i) ⦃ RawIMonad.rawMonad (rawMonadIT ⦃ M-monad ⦄) ⦄
    StateIT<:State ⦃ M-monad ⦄ = IState⇒State ⦃ rawMonadTI ⦃ RawIMonad.rawMonad M-monad ⦄ ⦄ (StateTI<:IState ⦃ RawIMonad.rawMonad M-monad ⦄)

    StateT<:Trans : ∀{S : Type ℓ} → Trans (StateT S)
    StateT<:Trans = record
        { lift = λ ⦃ M-monad ⦄ m → mkState λ s → RawIMonad.fmap M-monad (_, s) m
        }

instance
    _ = rawFunctor
    _ = rawApplicative
    _ = rawIApplicative
    _ = rawMonad
    _ = rawIMonad
    _ = StateTI<:IState
    _ = StateIT<:State
    _ = StateT<:Trans