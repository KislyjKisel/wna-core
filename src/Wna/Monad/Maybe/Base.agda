{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Maybe.Base where

open import Data.Maybe using (Maybe)
open import Function using (_∘′_)
open import Wna.Class.Monad.Trans using (MonT′; MonT)

MaybeT′ : MonT′
MaybeT′ = _∘′ Maybe

MaybeT : ∀{ℓ} → MonT ℓ ℓ
MaybeT = _∘′ Maybe
