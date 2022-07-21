{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Prelude where

open import Wna.Primitive

postulate
    seq : ∀{aℓ bℓ} {A : Type aℓ} {B : Type bℓ} → A → B → B

{-# COMPILE GHC seq = \ aℓ bℓ a b -> seq #-}
