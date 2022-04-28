{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Bundles where

open import Wna.Class.RawMonad using (RawMonad; module MkRawMonad)
open import Wna.Monad.Identity.Base
open import Wna.Monad.Trans

module _ {ℓ} where
    rawMonad : RawMonad (Identity {ℓ = ℓ})
    rawMonad = MkRawMonad.from:pure,>>= pure _>>=_

    open RawMonad rawMonad public
        using (rawApplicative; rawFunctor)
