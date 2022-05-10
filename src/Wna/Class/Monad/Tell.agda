{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Tell where

open import Data.Unit.Polymorphic                   using (⊤)
open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Primitive

record MonadTell {ℓ} (L : Type ℓ) (M : Fun ℓ) : Type (ℓ↑ ℓ) where
    field
        overlap ⦃ rawMonad ⦄ : RawMonad M

        tell : L → M ⊤

open MonadTell ⦃...⦄ public
    using (tell)
