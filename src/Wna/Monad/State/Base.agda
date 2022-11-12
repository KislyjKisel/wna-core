{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Base where

open import Data.Product                using (proj₁; proj₂; _×_; _,_)
open import Data.Unit.Polymorphic       using (⊤)
open import Function.Base               using (_$′_; _∘_; _∘′_)
open import Wna.Class.RawApplicative    using (IFun; Fun⇒IFun)
open import Wna.Class.RawFunctor        using (Fun)
open import Wna.Class.RawMonad          using (RawIMonad; RawMonad; module IMonadFT; module MonadFT)
open import Wna.Monad.Identity          using (Identity; runIdentity; mkIdentity)
open import Wna.Monad.Trans             using (MonT; MonIT; MonTI)
open import Wna.Primitive

record StateTI {ℓ} (M : Fun ℓ) (I J : Type ℓ) (A : Type ℓ) : Type ℓ where
    no-eta-equality
    pattern
    constructor makeTI
    field
        runTI : I → M (A × J)

    evalTI : ⦃ M-monad : RawMonad M ⦄ → I → M A
    evalTI ⦃ M-monad ⦄ = RawMonad.map M-monad proj₁ ∘ runTI

    execTI : ⦃ M-monad : RawMonad M ⦄ → I → M J
    execTI ⦃ M-monad ⦄ = RawMonad.map M-monad proj₂ ∘ runTI

open StateTI public
    using (runTI; evalTI; execTI)

StateI : ∀{ℓ} → IFun (Type ℓ) ℓ
StateI = StateTI Identity

StateT : ∀{ℓ} → Type ℓ → MonT ℓ ℓ
StateT S M = StateTI M S S

module _ {ℓ} {S : Type ℓ} {M} {A : Type ℓ} where

    makeT : (S → M (A × S)) → StateT S M A
    makeT f = makeTI f

    runT : StateT S M A → S → M (A × S)
    runT = runTI

    evalT : ⦃ M-monad : RawMonad M ⦄ → StateT S M A → S → M A
    evalT m = evalTI m

    execT : ⦃ M-monad : RawMonad M ⦄ → StateT S M A → S → M S
    execT m = execTI m

StateIT : ∀{ℓ} → Type ℓ → MonIT ℓ ℓ
StateIT S M i j = StateT S (M i j)

State : ∀{ℓ} → Type ℓ → Fun ℓ
State S = StateT S Identity

module _ {ℓ} {S : Type ℓ} {A : Type ℓ} where
    make : (S → A × S) → State S A
    make f = makeTI $′ mkIdentity ∘′ f

    run : State S A → S → A × S
    run (makeTI f) x = runIdentity $′ f x

    eval : State S A → S → A
    eval (makeTI f) x = proj₁ $′ runIdentity $′ f x

    exec : State S A → S → S
    exec (makeTI f) x = proj₂ $′ runIdentity $′ f x

pure : ∀{ℓ} {S : Type ℓ} → MonadFT.pure (State S)
pure x = makeTI λ s → mkIdentity (x , s)

_>>=_ : ∀{ℓ} {S : Type ℓ} → MonadFT._>>=_ (State S)
_>>=_ (makeTI x) f = makeTI λ s → mkIdentity
    let (y , s') = runIdentity (x s)
    in runIdentity $′ runTI (f y) s'

module _ {ℓ} {M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ where
    private
        module M = RawMonad M-monad

    pureTI : IMonadFT.pure (StateTI M)
    pureTI x = makeTI λ s → M.pure (x , s)

    _>>=TI_ : IMonadFT._>>=_ (StateTI M)
    (makeTI m) >>=TI f = makeTI λ i → m i M.>>= λ (a , j) → runTI (f a) j

    lift : ∀{S A : Type ℓ} → M A → StateT S M A
    lift m = makeTI λ s → (_, s) M.<$> m

    getTI : ∀{i} → StateTI M i i i
    getTI = makeTI λ i → M.pure (i , i)

    putTI : ∀{i j} → j → StateTI M i j ⊤
    putTI j = makeTI λ i → M.pure (_ , j)
