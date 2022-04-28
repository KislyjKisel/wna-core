{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Ask where

open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Primitive

record Ask {ℓ} (M : Fun ℓ) ⦃ M-monad : RawMonad M ⦄ : Type (ℓ↑ ℓ) where
    field
        E   : Type ℓ
        ask : M E

open Ask ⦃...⦄ public
    using (ask)
