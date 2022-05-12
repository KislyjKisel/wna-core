{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Class.Eq where

open import Data.Bool.Base using (Bool)
open import Wna.Primitive

postulate
    Eq : ∀{ℓ} → Type ℓ → Type ℓ

{-# FOREIGN GHC data AgdaEqDict _ a = Eq a => AgdaEqDict #-}
{-# COMPILE GHC Eq = type AgdaEqDict #-}

infix 4 _==_ _/=_

postulate
    _==_ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Eq A ⦄ → A → A → Bool
    _/=_ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Eq A ⦄ → A → A → Bool

-- todo: postulated properties?

{-# COMPILE GHC _==_ = \ ℓ A d -> (==) #-}
{-# COMPILE GHC _/=_ = \ ℓ A d -> (/=) #-}
