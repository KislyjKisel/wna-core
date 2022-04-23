{-# OPTIONS --without-K --safe #-}

module Wna.Data.Float.Instances where

open import Agda.Builtin.Int               using () renaming (Int to ℤ)
open import Agda.Builtin.Nat               using () renaming (Nat to ℕ)
open import Data.Bool.Base                 using (if_then_else_)
open import Data.Float.Base
open import Wna.Class.Cast                 using (Cast_⇒_)
open import Wna.Class.Numeric       as Num using ()
open import Wna.Class.RawEquality   as REq using ()
open import Wna.Class.RawOrder      as ROr using ()

-- todo: ℤ, Bool (join/meet), ℚ ?(perf - slow)

instance
    _ : Num.Negate Float
    _ = record { R = Float ; -_ = -_ }

    _ : Num.Add Float Float
    _ = record { R = Float ; _+_ = _+_ }

    _ : Num.Subtract Float Float
    _ = record { R = Float ; _-_ = _-_ }

    _ : Num.Multiply Float Float
    _ = record { R = Float ; _*_ = _*_ }

    _ : Num.Divide Float Float
    _ = record { R = Float ; _/_ = _÷_ }

    _ : Num.Square Float
    _ = record { R = Float ; _² = λ x → x * x }
    
    _ : Num.Power Float Float
    _ = record { R = Float ; _^_ = _**_ }

    _ : Num.Exponential Float
    _ = record { R = Float ; exp = e^_ }

    _ : Num.Absolute Float
    _ = record { R = Float ; abs = λ x → if x <ᵇ 0.0 then - x else x }

    _ : Num.Join Float Float
    _ = record { R = Float ; _∨_ = λ x y → if x <ᵇ y then y else x }

    _ : Num.Meet Float Float
    _ = record { R = Float ; _∧_ = λ x y → if x ≤ᵇ y then x else y }

    _ : ROr.RawStrictOrder Float Float
    _ = record { _<ᵇ_ = _<ᵇ_ }

    _ : ROr.RawOrder Float Float
    _ = record { _≤ᵇ_ = _≤ᵇ_ }

    _ : Cast ℕ ⇒ Float
    _ = record { cast = fromℕ }

    _ : Cast ℤ ⇒ Float
    _ = record { cast = fromℤ }
