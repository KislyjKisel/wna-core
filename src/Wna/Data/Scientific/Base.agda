{-# OPTIONS --without-K --safe #-}

module Wna.Data.Scientific.Base where

open import Data.Integer.Base using (ℤ)
open import Wna.Primitive

record Scientific : Type where
    constructor mkScientific
    field
        coefficient exponent₁₀ : ℤ

open Scientific public
    using (coefficient; exponent₁₀)
