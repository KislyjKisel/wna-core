{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Base where

open import Data.Sum using (_⊎_)
open import Wna.Class.Monad.Trans using (MonT)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Monad.Identity.Base using (Identity)

record ExceptT {ℓ} (E : Type ℓ) (M : Fun ℓ) (A : Type ℓ) : Type ℓ where
    inductive
    no-eta-equality
    pattern
    constructor mkExcept
    field
        runExcept : M (E ⊎ A)

open ExceptT public

Except : ∀{ℓ} (E : Type ℓ) → Fun ℓ
Except E = ExceptT E Identity
