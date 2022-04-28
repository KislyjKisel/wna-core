{-# OPTIONS --without-K --safe #-}

module Wna.Data.Float.Instances where

open import Agda.Builtin.Int        using () renaming (Int to ℤ)
open import Agda.Builtin.Nat        using () renaming (Nat to ℕ)
open import Wna.Class.Cast          using (Cast_⇒_)
open import Wna.Class.Numeric       as Num using ()
open import Wna.Class.RawEquality   as REq using ()
open import Wna.Class.RawOrder      as ROr using ()
open import Wna.Data.Float

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
    _ = record { R = Float ; _² = _² }
    
    _ : Num.Reciprocal Float
    _ = record { R = Float ; 1/_ = 1/_ }
    
    _ : Num.Power Float Float
    _ = record { R = Float ; _^_ = _**_ }

    _ : Num.Exponential Float
    _ = record { R = Float ; exp = e^_ }

    _ : Num.Absolute Float
    _ = record { R = Float ; abs = abs }

    _ : Num.Join Float Float
    _ = record { R = Float ; _∨_ = _∨_ }

    _ : Num.Meet Float Float
    _ = record { R = Float ; _∧_ = _∧_ }

    _ : ROr.RawStrictOrder Float Float
    _ = record { _<ᵇ_ = _<ᵇ_ }

    _ : ROr.RawOrder Float Float
    _ = record { _≤ᵇ_ = _≤ᵇ_ }

    _ : Cast ℕ ⇒ Float
    _ = record { cast = fromℕ }

    _ : Cast ℤ ⇒ Float
    _ = record { cast = fromℤ }
