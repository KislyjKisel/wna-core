{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.State where

open import Data.Unit.Polymorphic                       using (⊤)
open import Wna.Class.RawApplicative                    using (IFun)
open import Wna.Class.RawApplicative.LevelPolymorphic   using (IFun′)
open import Wna.Class.RawFunctor                        using (Fun)
open import Wna.Class.RawFunctor.LevelPolymorphic       using (Fun′)
open import Wna.Class.RawMonad                          using (RawMonad; RawIMonad)
open import Wna.Class.RawMonad.LevelPolymorphic         using (RawIMonad′)
open import Wna.Class.RawMonad.LevelPolymorphic         using (RawMonad′)
open import Wna.Primitive

record State {ℓ} (M : Fun ℓ) ⦃ M-monad : RawMonad M ⦄ : Type (ℓ↑ ℓ) where
    field
        S   : Type ℓ
        get : M S
        put : S → M ⊤

open State ⦃...⦄ public
    using (get; put)

record State′ (M : Fun′) ⦃ M-monad : RawMonad′ M ⦄ : Typeω where
    field
        {sℓ}  : Level
        S     : Type sℓ
        get′  : M S
        put′  : S → M (⊤ {sℓ})

open State′ ⦃...⦄ public
    using (get′; put′)

record IState {ℓ} (M : IFun (Type ℓ) ℓ ) ⦃ M-monad : RawIMonad M ⦄ : Type (ℓ↑ ℓ) where
    field
        iget : ∀{i} → M i i i
        iput : ∀{i j} → j → M i j ⊤

open IState ⦃...⦄ public
    using (iget; iput)

-- IState⇒State : ∀{ℓ} {M : IFun (Type ℓ) ℓ} ⦃ M-monad : RawIMonad M ⦄ →
--                IState M ⦃ M-monad ⦄ → ∀{i : Type ℓ} → State (M i i) ⦃ RawIMonad.rawMonad M-monad ⦄
-- IState⇒State ist {i = i} = record
--     { S   = i
--     ; get = IState.iget ist
--     ; put = IState.iput ist
--     }

record IState′ {ℓ} (M : IFun′ (Type ℓ) ) ⦃ M-monad : RawIMonad′ M ⦄ : Typeω where
    field
        iget′ : ∀{i} → M i i i
        iput′ : ∀{i j} → j → M i j (⊤ {ℓ})

open IState′ ⦃...⦄ public
    using (iget′; iput′)

-- IState′⇒State′ : ∀{ℓ} {M : IFun′ (Type ℓ)} ⦃ M-monad : RawIMonad′ M ⦄ →
--                  IState′ M ⦃ M-monad ⦄ → ∀{i : Type ℓ} → State′ (M i i) ⦃ RawIMonad′.rawMonad′ M-monad ⦄
-- IState′⇒State′ ist {i = i} = record
--     { S    = i
--     ; get′ = IState′.iget′ ist
--     ; put′ = IState′.iput′ ist
--     }
