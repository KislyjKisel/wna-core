{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawApplicative.Instanced where

open import Wna.Class.RawApplicative using (RawIApplicative)

open RawIApplicative ⦃...⦄ public
    hiding (rawFunctor)
