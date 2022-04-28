{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawMonad.Instanced where

open import Wna.Class.RawMonad using (RawIMonad)

open RawIMonad ⦃...⦄ public
    hiding (rawIApplicative)
