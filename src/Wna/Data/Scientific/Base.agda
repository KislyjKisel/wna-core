{-# OPTIONS --without-K --safe #-}

module Wna.Data.Scientific.Base where

open import Data.Integer.Base as ℤ using (ℤ)
open import Data.Nat.Base as ℕ using (nonZero)
open import Data.Integer.Properties as ℤp using ()
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Wna.Primitive

record Scientific : Type where
    constructor mkScientific
    field
        coefficient exponent₁₀ : ℤ

open Scientific public
    using (coefficient; exponent₁₀)

-_ : Scientific → Scientific
-_ (mkScientific c e) = mkScientific (ℤ.- c) e 

-- todo: arithmetic

private
    normalizePositive : ℤ → ℤ → Scientific
    normalizePositive c e with c ℤ.% (ℤ.+ 10)
    ... | ℕ.zero = normalizePositive (c ℤ./ (ℤ.+ 10)) ((ℤ.+ 1) ℤ.+ e)
    ... | r      = mkScientific c e

    -- todo: WF recursion on `c`

normalize : Scientific → Scientific
normalize (mkScientific c e) with ℤp.<-cmp c (ℤ.+ 0)
... | tri< < ≉ ≯ = - (normalizePositive (ℤ.- c) e)
... | tri≈ ≮ ≈ ≯ = mkScientific (ℤ.+ 0) (ℤ.+ 0)
... | tri> ≮ ≉ > = normalizePositive c e 

-- todo: data Isℤ : Scientific → Type where

