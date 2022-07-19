{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Eq where

open import Data.Bool.Base using (Bool)
open import Wna.Primitive

postulate
    Eq : ∀{ℓ} → Type ℓ → Type ℓ

{-# FOREIGN GHC data AgdaEqDict a b = Eq b => AgdaEqDict #-}
{-# COMPILE GHC Eq = type AgdaEqDict #-}

infix 4 _==_ _/=_

postulate
    _==_ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Eq A ⦄ → A → A → Bool
    _/=_ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Eq A ⦄ → A → A → Bool

-- todo: postulated properties?

{-# COMPILE GHC _==_ = \ ℓ a AgdaEqDict -> (==) #-}
{-# COMPILE GHC _/=_ = \ ℓ a AgdaEqDict -> (/=) #-}
