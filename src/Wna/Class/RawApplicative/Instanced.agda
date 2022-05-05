{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawApplicative.Instanced where

open import Wna.Class.RawApplicative using (RawIApplicative)

open RawIApplicative ⦃...⦄ public
    using
    ( pure ; liftA2
    ; _<*>_ ; _<*_ ; _*>_
    )
