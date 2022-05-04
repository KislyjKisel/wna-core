{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Ask where

open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record Ask {ℓ} (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M
        
        E   : Type ℓ
        ask : M E

open Ask ⦃...⦄ public
    using (ask)
