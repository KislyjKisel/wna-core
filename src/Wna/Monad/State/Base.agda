{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Base where

open import Data.Product                using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Polymorphic       using (⊤)
open import Function.Base               using (_∘′_)
open import Wna.Class.RawApplicative    using (IFun; Fun⇒IFun)
open import Wna.Class.RawFunctor        using (Fun)
open import Wna.Class.RawMonad          using (RawIMonad; RawMonad; module IMonadFT)
open import Wna.Monad.Identity          using (Identity; runIdentity; mkIdentity)
open import Wna.Monad.Trans             using (MonT; MonIT; MonTI)
open import Wna.Primitive

record StateTI {ℓ} (M : Fun ℓ) (i j : Type ℓ) (A : Type ℓ) : Type ℓ where
    no-eta-equality
    pattern
    constructor mkState
    field
        runState : i → M (A × j)

    evalState : ⦃ M-monad : RawMonad M ⦄ → i → M A
    evalState ⦃ M-monad ⦄ = map proj₁ ∘′ runState
        where
            open RawMonad M-monad using (map)

    execState : ⦃ M-monad : RawMonad M ⦄ → i → M j
    execState ⦃ M-monad ⦄ = map proj₂ ∘′ runState
        where
            open RawMonad M-monad using (map)

open StateTI public

IState : ∀{ℓ} → IFun (Type ℓ) ℓ
IState = StateTI Identity

StateT : ∀{ℓ} → Type ℓ → MonT ℓ ℓ
StateT S M = StateTI M S S

StateIT : ∀{ℓ} → Type ℓ → MonIT ℓ ℓ
StateIT S M i j = StateT S (M i j)

State : ∀{ℓ} → Type ℓ → Fun ℓ
State S = StateT S Identity

mkState′ : ∀{ℓ} {S A : Type ℓ} → (S → A × S) → State S A
mkState′ f = mkState (mkIdentity ∘′ f)

runState′ : ∀{ℓ} {S A : Type ℓ} → State S A → S → A × S
runState′ (mkState f) x = runIdentity (f x)

evalState′ : ∀{ℓ} {S A : Type ℓ} → State S A → S → A
evalState′ (mkState f) x = proj₁ (runIdentity (f x))

execState′ : ∀{ℓ} {S A : Type ℓ} → State S A → S → S
execState′ (mkState f) x = proj₂ (runIdentity (f x))

module _ {ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ where
    private
        module M = RawMonad M-monad

    pure : IMonadFT.pure (StateTI M)
    pure x = mkState λ s → M.pure (x , s)

    _>>=_ : IMonadFT._>>=_ (StateTI M)
    (mkState m) >>= f = mkState λ i → m i M.>>= λ (a , j) → runState (f a) j

    lift : ∀{S A : Type ℓ} → M A → StateT S M A
    lift m = mkState λ s → (_, s) M.<$> m

    iget : ∀{i} → StateTI M i i i
    iget = mkState λ i → M.pure (i , i)

    iput : ∀{i j} → j → StateTI M i j ⊤
    iput j = mkState λ i → M.pure (_ , j)
