{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawMonoid where

open import Algebra.Bundles as Ab using ()
open import Data.Product using (Σ; _,_)
open import Wna.Primitive

record RawMonoid {ℓ} (A : Type ℓ) : Type ℓ where
    field
        mappend : A → A → A
        mempty  : A

open RawMonoid ⦃...⦄ public
    using (mappend; mempty)

from-std : ∀{aℓ rℓ} → Ab.RawMonoid aℓ rℓ → Σ (Type aℓ) RawMonoid
from-std sm = Carrier , record { mappend = _∙_ ; mempty = ε }
    where open Ab.RawMonoid sm
