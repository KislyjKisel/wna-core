{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Maybe.Instances where

open import Data.Maybe using (just)
open import Wna.Class.RawMonad using (RawMonad)
open import Wna.Class.RawMonad.LevelPolymorphic using (RawMonad′)
open import Wna.Class.Monad.Trans
open import Wna.Monad.Maybe.Base
open import Wna.Monad.Maybe.Properties

MaybeT′<:Trans′ : Trans′ (MaybeT′)
MaybeT′<:Trans′ = record
    { lift′ = λ ⦃ M-monad ⦄ m → RawMonad′.fmap′ M-monad just m
    }

MaybeT<:Trans : ∀{ℓ} → Trans (MaybeT {ℓ})
MaybeT<:Trans = record
    { lift = λ ⦃ M-monad ⦄ m → RawMonad.fmap M-monad just m
    }

instance
    _ = rawFunctor
    _ = rawFunctor′
    _ = rawApplicative
    _ = rawApplicative′
    _ = rawMonad
    _ = rawMonad′
    _ = MaybeT′<:Trans′
    _ = MaybeT<:Trans
