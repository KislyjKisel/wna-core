{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Instances where

open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘′_)
open import Wna.Class.RawMonad using (RawMonad)
open import Wna.Class.Monad.Handle
open import Wna.Class.Monad.Raise
open import Wna.Class.Monad.Trans
open import Wna.Monad.Except.Base
open import Wna.Monad.Except.Properties

module _ {eℓ} {E : Type eℓ} where

    Except<:Raise : ∀{M} ⦃ M-monad : RawMonad M ⦄ → Raise (ExceptT E M) ⦃ rawMonadT ⦃ M-monad ⦄ ⦄
    Except<:Raise ⦃ M-monad ⦄ = record
        { E     = E
        ; raise = λ e → mkExcept ((RawMonad.pure M-monad) (inj₁ e))
        }

    Except<:Handle : ∀{M} ⦃ M-monad : RawMonad M ⦄ → Handle (ExceptT E M) ⦃ rawMonadT ⦃ M-monad ⦄ ⦄
    Except<:Handle ⦃ M-monad ⦄ = record
        { E      = E
        ; handle = λ{ (mkExcept m) h → mkExcept (m >>= λ{ (inj₁ e) → runExcept (h e)
                                                        ; (inj₂ a) → pure (inj₂ a)
                                                        })
                    }
        }
        where open RawMonad M-monad

    ExceptT<:Trans : Trans (ExceptT E)
    ExceptT<:Trans = record
        { lift = λ ⦃ M-monad ⦄ → mkExcept ∘′ RawMonad.fmap M-monad inj₂
        }


instance
    _ = rawFunctor
    _ = rawApplicative
    _ = rawMonad
    _ = Except<:Raise
    _ = Except<:Handle
    _ = ExceptT<:Trans
