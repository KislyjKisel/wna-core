{-# OPTIONS --without-K --safe #-}

module Wna.Data.Nat.Instances where

open import Data.Nat
open import Wna.Class.DecEquality   as DEq using ()
open import Wna.Class.DecOrder      as DOr using ()
open import Wna.Class.Numeric       as Num using ()
open import Wna.Class.RawEquality   as REq using ()
open import Wna.Class.RawOrder      as ROr using ()

instance
    _ : Num.Add ℕ ℕ
    _ = record { R = ℕ ; _+_ = _+_ }

    _ : Num.Subtract ℕ ℕ
    _ = record { R = ℕ ; _-_ = _∸_ }

    _ : Num.Multiply ℕ ℕ
    _ = record { R = ℕ ; _*_ = _*_ }

    _ : Num.Square ℕ
    _ = record { R = ℕ ; _² = λ x → x * x }
    
    _ : Num.Power ℕ ℕ
    _ = record { R = ℕ ; _^_ = _^_ }

    _ : Num.Join ℕ ℕ
    _ = record { R = ℕ ; _∨_ = _⊔_ }

    _ : Num.Meet ℕ ℕ
    _ = record { R = ℕ ; _∧_ = _⊓_ }

    _ : REq.RawEquality ℕ ℕ
    _ = from:_≡ᵇ_ _≡ᵇ_
        where open REq.MkRawEquality ℕ ℕ

    _ : ROr.RawStrictOrder ℕ ℕ
    _ = record { _<ᵇ_ = _<ᵇ_ }

    _ : ROr.RawOrder ℕ ℕ
    _ = record { _≤ᵇ_ = _≤ᵇ_ }

    _ : DOr.DecStrictOrder ℕ ℕ
    _ = record { _<?_ = _<?_ }

    _ : DOr.DecOrder ℕ ℕ
    _ = record { _≤?_ = _≤?_ }
