{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Local where

open import Data.Unit                               using (⊤)
open import Wna.Class.Monad.Ask                     using (Ask)
open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Primitive

record Local {ℓ} (M : Fun ℓ) ⦃ M-monad : RawMonad M ⦄ : Type (ℓ↑ ℓ) where
    field ⦃ M-ask ⦄ : Ask M
    open Ask M-ask
    field local : (E → E) → {A : Type ℓ} → M A → M A

open Local ⦃...⦄ public
    using (local)
