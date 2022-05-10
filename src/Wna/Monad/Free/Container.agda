{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Free.Container where

open import Data.Container.Combinator as Cc using ()
open import Data.Container.Core             using (Container)
open import Wna.Primitive

FreeC : ∀{ℓ} (F M : Container ℓ ℓ) → Type ℓ → Container ℓ ℓ
FreeC F M A = M Cc.∘ (F Cc.⊎ Cc.const A)
