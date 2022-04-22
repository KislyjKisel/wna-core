{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Instances where

open import Function using (const; _∘′_)
open import Wna.Class.RawMonad using (RawIMonad)
open import Wna.Class.Monad.Ask
open import Wna.Class.Monad.Local
open import Wna.Class.Monad.Trans
open import Wna.Monad.Reader.Base
open import Wna.Monad.Reader.Properties

module _ {rℓ} {R : Type rℓ} where

    ReaderIT<:Ask : ∀{M i j} ⦃ M-monad : RawIMonad M ⦄ → Ask (ReaderIT R M i j) ⦃ rawMonadIT M-monad ⦄
    ReaderIT<:Ask ⦃ M-monad ⦄ = record
        { E   = R
        ; ask = mkReader (RawIMonad.pure M-monad)
        }

    ReaderIT<:Local : ∀{M i j} ⦃ M-monad : RawIMonad M ⦄ → Local (ReaderIT R M i j) ⦃ rawMonadIT M-monad ⦄
    ReaderIT<:Local ⦃ M-monad ⦄ = record
        { local = λ f m → mkReader λ r → runReader m (f r)
        ; M-ask = ReaderIT<:Ask
        }

    ReaderT<:Trans : Trans (ReaderT R)
    ReaderT<:Trans = record
        { lift = λ ⦃ M-monad ⦄ → mkReader ∘′ const  
        }

instance
    _ = rawFunctor
    _ = rawApplicative
    _ = rawMonad
    _ = ReaderIT<:Ask
    _ = ReaderIT<:Local
    _ = ReaderT<:Trans
