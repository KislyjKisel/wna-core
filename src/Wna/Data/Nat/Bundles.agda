{-# OPTIONS --without-K --safe #-}

module Wna.Data.Nat.Bundles where

open import Data.Nat
open import Data.Nat.Properties            using (nonZero?)
open import Function.Base                  using (const)
open import Wna.Class.DecEquality   as DEq using ()
open import Wna.Class.DecOrder      as DOr using ()
open import Wna.Class.Numeric       as Num using ()
open import Wna.Class.RawEquality   as REq using ()
open import Wna.Class.RawOrder      as ROr using ()

add : Num.Add ℕ ℕ
add = record { R = ℕ ; _+_ = _+_ }

subtract : Num.Subtract ℕ ℕ
subtract = record { R = ℕ ; _-_ = _∸_ }

multiply : Num.Multiply ℕ ℕ
multiply = record { R = ℕ ; _*_ = _*_ }

modulo : Num.Modulo ℕ (const ℕ)
modulo = Num.mkModulo′ (λ x y p → _%_ x y ⦃ p ⦄) λ _ y → nonZero? y

square : Num.Square ℕ
square = record { R = ℕ ; _² = λ x → x * x }

power : Num.Power ℕ ℕ
power = record { R = ℕ ; _^_ = _^_ }

join : Num.Join ℕ ℕ
join = record { R = ℕ ; _∨_ = _⊔_ }

meet : Num.Meet ℕ ℕ
meet = record { R = ℕ ; _∧_ = _⊓_ }

rawEquality : REq.RawEquality ℕ ℕ
rawEquality = from:_≡ᵇ_ _≡ᵇ_
    where open REq.MkRawEquality ℕ ℕ

rawStrictOrder : ROr.RawStrictOrder ℕ ℕ
rawStrictOrder = record { _<ᵇ_ = _<ᵇ_ }

rawOrder : ROr.RawOrder ℕ ℕ
rawOrder = record { _≤ᵇ_ = _≤ᵇ_ }

decPropEquality : DEq.DecPropositionalEquality ℕ
decPropEquality = record { _≡?_ = _≟_ }

decStrictOrder : DOr.DecStrictOrder ℕ ℕ
decStrictOrder = record { _<?_ = _<?_ }

decOrder : DOr.DecOrder ℕ ℕ
decOrder = record { _≤?_ = _≤?_ }
