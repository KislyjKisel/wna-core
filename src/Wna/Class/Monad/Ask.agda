{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Ask where

open import Wna.Class.RawFunctor using (Fun)
open import Wna.Class.RawMonad   using (RawMonad)
open import Wna.Primitive

record MonadAsk {ℓ} (E : Type ℓ) (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M
        
        ask : M E

module Instanced where
    open MonadAsk ⦃...⦄ public
        using (ask)
