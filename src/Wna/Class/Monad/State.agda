{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.State where

open import Data.Unit.Polymorphic                       using (⊤)
open import Wna.Class.RawApplicative                    using (IFun)
open import Wna.Class.RawFunctor                        using (Fun)
open import Wna.Class.RawMonad                          using (RawMonad; RawIMonad)
open import Wna.Primitive

record MonadState {ℓ} (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M

        S   : Type ℓ
        get : M S
        put : S → M ⊤
    
    modify : (S → S) → M ⊤
    modify f = let open RawMonad rawMonad in do
        x ← get
        put (f x)
        pure _

    gets : ∀{A} → (S → A) → M A
    gets f = let open RawMonad rawMonad in do
        x ← get
        pure (f x)

open MonadState ⦃...⦄ public
    using (get; put; modify; gets)

record IMonadState {ℓ} (M : IFun (Type ℓ) ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawIMonad ⦄ : RawIMonad M
        
        iget : ∀{i} → M i i i
        iput : ∀{i j} → j → M i j ⊤

    imodify : ∀{i j} → (i → j) → M i j ⊤
    imodify f = let open RawIMonad rawIMonad in do
        x ← iget
        iput (f x)
        pure _

    igets : ∀{i A} → (i → A) → M i i A
    igets f = let open RawIMonad rawIMonad in do
        x ← iget
        pure (f x)

open IMonadState ⦃...⦄ public
    using (iget; iput; imodify; igets)

-- IState⇒State : ∀{ℓ} {M : IFun (Type ℓ) ℓ} ⦃ M-monad : RawIMonad M ⦄ →
--                IState M ⦃ M-monad ⦄ → ∀{i : Type ℓ} → State (M i i) ⦃ RawIMonad.rawMonad M-monad ⦄
-- IState⇒State ist {i = i} = record
--     { S   = i
--     ; get = IState.iget ist
--     ; put = IState.iput ist
--     }
