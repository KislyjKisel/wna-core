{-# OPTIONS --without-K --safe #-}

module Wna.Data.Vec where

open import Data.List.Base using (List)
open import Data.Fin.Base using (Fin)
open import Wna.Primitive

open import Data.Vec.Base public

arrange : ∀{n ℓ} {A : Type ℓ} → (A → Fin n) → List A → Vec (List A) n
arrange f List.[]       = replicate List.[]
arrange f (x List.∷ xs) = arrange f xs [ f x ]%= (x List.∷_)
