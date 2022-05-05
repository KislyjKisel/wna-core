{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monad.Trans where

open import Wna.Monad.Trans
open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawMonad                      using (RawMonad)
open import Wna.Primitive

record MonadTrans {ℓ} (T : MonT ℓ ℓ) : Type (ℓ↑ ℓ) where
    field
        lift : ∀{M : Fun ℓ} ⦃ M-monad : RawMonad M ⦄ {A : Type ℓ} → M A → T M A

open MonadTrans ⦃...⦄ public
    using (lift)
