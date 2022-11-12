{-# OPTIONS --without-K --safe #-}

module Wna.Data.Container.Base where

open import Data.Container.Combinator using (_⊎_)
open import Data.Container.Core       using (Container; _▷_)
open import Data.Empty.Polymorphic    using (⊥)
open import Data.List.Base            using (List; foldr)

void : ∀{sℓ pℓ} → Container sℓ pℓ
void = ⊥ ▷ λ ()

⨁_ : ∀{sℓ pℓ} → List (Container sℓ pℓ) → Container sℓ pℓ
⨁_ = foldr _⊎_ void
