{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Properties where

open import Function using (id; flip; _$_; _∘_; const)
open import Relation.Binary.PropositionalEquality using (refl)
open import Wna.Class.Monad using (Monad; IMonad)
open import Wna.Class.Monad.Trans using (RawMonadT; RawMonadIT)
open import Wna.Class.RawApplicative using (module MkRawIApplicative)
open import Wna.Class.RawMonad using (RawMonad; RawIMonad; module IMonadFT; module MkRawIMonad)
open import Wna.Monad.Identity using () renaming (rawMonad to id-rawMonad)
open import Wna.Monad.Reader.Base

module _ {rℓ} {R : Type rℓ} where

    rawMonadIT : RawMonadIT (ReaderIT R)
    rawMonadIT {I = I} {F = M'} M = record
        { rawIApplicative = MkRawIApplicative.from:pure,<*> (mkReader ∘ const ∘ pure) (λ{ (mkReader f) (mkReader x) → mkReader $ λ r → f r <*> x r })
        ; _>>=_           = bind
        ; join            = λ {_} {i} {j} {k} → MkRawIMonad.>>=⇒join {F = ReaderIT R M'} bind
        }
        where
        open RawIMonad M
        bind : IMonadFT._>>=_ (ReaderIT R M')
        bind (mkReader x) f = mkReader λ r → x r >>= flip runReader r ∘ f

    rawMonadT : RawMonadT (ReaderT R)
    rawMonadT M = rawMonadIT M
        where
        open RawMonad M

    rawMonad : RawMonad (Reader R)
    rawMonad = rawMonadT id-rawMonad

    open RawMonad rawMonad public using
        ( rawApplicative
        ; rawFunctor
        )
