{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Interface where

import Wna.Class.Monad.Handle as Handle
import Wna.Class.Monad.Raise as Raise
import Wna.Monad.Identity.Properties as Id
open import Wna.Monad.Except.Base
open import Wna.Monad.Except.Instances using (Except<:Raise; Except<:Handle)
open import Wna.Monad.Except.Properties

module _ {ℓ} {E : Type ℓ} where

    raise : E → ∀{A : Type ℓ} → Except E A
    raise = Raise.raise ⦃ rawMonad ⦄ ⦃ Except<:Raise ⦃ Id.rawMonad ⦄ ⦄

    handle : ∀{A : Type ℓ} → Except E A → (E → Except E A) → Except E A
    handle = Handle.handle ⦃ rawMonad ⦄ ⦃ Except<:Handle ⦃ Id.rawMonad ⦄ ⦄
