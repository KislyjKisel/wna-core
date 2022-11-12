{-# OPTIONS --without-K --safe #-}

module Wna.Data.Sum.Effectful.Left.Transformer where

open import Level using (Level)
open import Data.Sum.Base using (inj₁)
open import Effect.Monad using (RawMonad)

open import Data.Sum.Effectful.Left.Transformer public

private
    variable
        aℓ : Level
        A E : Set aℓ
        M : Set aℓ → Set aℓ


throw : ⦃ RawMonad M ⦄ → E → SumₗT E _ M A
throw ⦃ M[M] ⦄ e = mkSumₗT (RawMonad.pure M[M] (inj₁ e))
