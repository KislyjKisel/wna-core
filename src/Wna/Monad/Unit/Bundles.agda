{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Unit.Bundles where

open import Wna.Class.RawMonad using (RawMonad; module MkRawMonad)
open import Wna.Monad.Unit.Base

module _ {ℓ} where
    rawMonad       = MkRawMonad.from:pure,>>= {aℓ = ℓ} pure _>>=_
    rawFunctor     = RawMonad.rawFunctor rawMonad
    rawApplicative = RawMonad.rawApplicative rawMonad
