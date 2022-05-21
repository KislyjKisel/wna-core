{-# OPTIONS --without-K --safe #-}

module Wna.Data.Float.Bundles where

open import Wna.Class.Cast                 using (Cast[_⇒_])
open import Wna.Class.Numeric       as Num using ()
open import Wna.Class.RawEquality   as REq using ()
open import Wna.Class.RawOrder      as ROr using ()
open import Wna.Data.Float.Base
open import Wna.Data.Integer.Base          using (ℤ)
open import Wna.Data.Nat.Base              using (ℕ)
open import Wna.Data.Nat.Properties as ℕ   using ()

-- Conversion

cast-fromℕ : Cast[ ℕ ⇒ Float ]
cast-fromℕ = record { cast = fromℕ }

cast-fromℤ : Cast[ ℤ ⇒ Float ]
cast-fromℤ = record { cast = fromℤ }

-- Numeric

negate : Num.Negate Float
negate = Num.mkNegate‵′ (-_)

add : Num.Add Float Float
add = record { R = Float ; _+_ = _+_ }

subtract : Num.Subtract Float Float
subtract = record { R = Float ; _-_ = _-_ }

multiply : Num.Multiply Float Float
multiply = record { R = Float ; _*_ = _*_ }

divide : Num.Divide Float Float
divide = record { R = Float ; _/_ = _÷_ }

square : Num.Square Float
square = record { R = Float ; _² = _² }

reciprocal : Num.Reciprocal Float
reciprocal = record { R = Float ; 1/_ = 1/_ }

power : Num.Power Float Float
power = record { R = Float ; _^_ = _**_ }

exponential : Num.Exponential Float
exponential = record { R = Float ; exp = e^_ }

absolute : Num.Absolute Float
absolute = record { R = Float ; abs = abs }

join : Num.Join Float Float
join = record { R = Float ; _∨_ = _∨_ }

meet : Num.Meet Float Float
meet = record { R = Float ; _∧_ = _∧_ }

rawStrictOrder : ROr.RawStrictOrder Float Float
rawStrictOrder = record { _<ᵇ_ = _<ᵇ_ }

rawOrder : ROr.RawOrder Float Float
rawOrder = record { _≤ᵇ_ = _≤ᵇ_ }
