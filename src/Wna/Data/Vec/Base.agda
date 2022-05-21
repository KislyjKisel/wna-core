{-# OPTIONS --without-K --safe #-}

module Wna.Data.Vec.Base where

open import Data.Fin.Base  using (Fin)
open import Data.List.Base using (List)
open import Wna.Class.Traversable using (module TraversableFT)
open import Wna.Class.RawApplicative using () renaming (module Instanced to RaInst)
open import Wna.Primitive

open import Data.Vec.Base public

arrange : ∀{n ℓ} {A : Type ℓ} → (A → Fin n) → List A → Vec (List A) n
arrange f List.[]       = replicate List.[]
arrange f (x List.∷ xs) = arrange f xs [ f x ]%= (x List.∷_)

traverse : ∀{n ℓ} → TraversableFT.traverse (λ A → Vec {a = ℓ} A n)
traverse f [] = RaInst.pure []
traverse f (x ∷ xs) = RaInst.liftA2 _∷_ (f x) (traverse f xs)
