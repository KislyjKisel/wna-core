{-# OPTIONS --without-K --safe #-}

module Wna.Instances.Monoid.List where

open import Wna.Class.Monoid
open import Data.List.Base using (List; _++_; [])

List-Monoid : ∀{aℓ}{A : Set aℓ} → Monoid (List A)
List-Monoid = record { ε = [] ; _<>_ = _++_ }
