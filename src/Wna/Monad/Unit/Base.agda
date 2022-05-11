{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Unit.Base where

open import Data.Unit.Polymorphic using (⊤)
open import Function.Base         using (const)
open import Wna.Primitive

-- ? UnitT

record Unit {ℓ} (A : Type ℓ) : Type ℓ where
    constructor mkUnit
    field
        runUnit : ⊤ {ℓ}

open Unit public
    using (runUnit)

pure : ∀{ℓ} {A : Type ℓ} → A → Unit A
pure _ = _

_>>=_ : ∀{ℓ} {A B : Type ℓ} → Unit A → (A → Unit B) → Unit B
_ >>= _ = _ 


