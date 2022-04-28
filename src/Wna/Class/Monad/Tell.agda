{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Tell where

open import Data.Unit.Polymorphic                   using (⊤)
open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Primitive

record Tell {ℓ} (M : Fun ℓ) ⦃ M-monad : RawMonad M ⦄ : Type (ℓ↑ ℓ) where
    field
        L    : Type ℓ
        tell : L → M ⊤

open Tell ⦃...⦄ public
    using (tell)
