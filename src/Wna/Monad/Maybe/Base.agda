{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Maybe.Base where

open import Function.Base                           using (_∘′_)
open import Wna.Monad.Trans                         using (MonT; MonT′)
open import Wna.Class.RawFunctor                    using (Fun)
open import Wna.Class.RawMonad                      using (RawMonad; module MonadFT)
open import Wna.Class.RawFunctor.LevelPolymorphic   using (Fun′)
open import Wna.Class.RawMonad.LevelPolymorphic     using (RawMonad′; module MonadFT′)
open import Wna.Primitive

open import Data.Maybe.Base public
    renaming (_>>=_ to mb-bind)

MaybeT′ : MonT′
MaybeT′ = _∘′ Maybe

MaybeT : ∀{ℓ} → MonT ℓ ℓ
MaybeT = _∘′ Maybe

pure′ : ∀{M : Fun′} ⦃ _ : RawMonad′ M ⦄ → MonadFT′.pure′ (MaybeT′ M)
pure′ ⦃ M-monad ⦄ = RawMonad′.return′ M-monad ∘′ just

_>>=′_ : ∀{M : Fun′} ⦃ _ : RawMonad′ M ⦄ → MonadFT′._>>=′_ (MaybeT′ M)
_>>=′_ ⦃ M-monad ⦄ x f = x M.>>=′ maybe′ f (M.return′ nothing)
    where module M = RawMonad′ M-monad

pure : ∀{ℓ} {M : Fun ℓ} ⦃ _ : RawMonad M ⦄ → MonadFT.pure (MaybeT M)
pure ⦃ M-monad ⦄ = RawMonad.return M-monad ∘′ just

_>>=_ : ∀{ℓ} {M : Fun ℓ} ⦃ _ : RawMonad M ⦄ → MonadFT._>>=_ (MaybeT M)
_>>=_ ⦃ M-monad ⦄ x f = x M.>>= maybe′ f (M.return nothing)
    where module M = RawMonad M-monad

lift : ∀{ℓ} {M} ⦃ M-monad : RawMonad M ⦄ {A : Type ℓ} → M A → MaybeT M A
lift ⦃ M-monad ⦄ m = RawMonad.fmap M-monad just m

lift′ : ∀{M : Fun′} ⦃ M-monad : RawMonad′ M ⦄ {aℓ} {A : Type aℓ} → M A → MaybeT′ M A
lift′ ⦃ M-monad ⦄ m = RawMonad′.fmap′ M-monad just m
