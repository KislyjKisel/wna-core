{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Bundles where

open import Data.Container.Core      using (Container; map; ⟦_⟧)
open import Data.Product             using (_,_)
open import Effect.Functor           using (RawFunctor)
open import Level               as ℓ using (Level)
open import Wna.Class.Universe       using (Universe; universe)

private
    variable
        sℓ pℓ ℓ : Level


universe₁ : Universe 1 (ℓ , _) (ℓ ℓ.⊔ sℓ ℓ.⊔ pℓ) (Container sℓ pℓ)
universe₁ = universe ⟦_⟧

universe₀ : Set ℓ → Universe 0 _ (ℓ ℓ.⊔ sℓ ℓ.⊔ pℓ) (Container sℓ pℓ)
universe₀ A = universe λ C → ⟦ C ⟧ A

functor : ∀{sℓ pℓ ℓ} {C : Container sℓ pℓ} → RawFunctor {ℓ} ⟦ C ⟧
functor {C = C} = record { _<$>_ = map }
