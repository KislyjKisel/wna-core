{-# OPTIONS --without-K --safe #-}

module Wna.Data.List.Base where

open import Data.List.Relation.Unary.All as All  using (All)
open import Data.Product                         using (Σ; _,_)
open import Function.Base                        using (_$′_)
open import Wna.Class.RawApplicative             using () renaming (module Instanced to RaInst)
open import Wna.Class.Traversable                using (module TraversableFT)
open import Wna.Primitive
open import Wna.Serialization.Json       as Json using ()

open import Data.List.Base public

traverse : ∀{ℓ} → TraversableFT.traverse (List {ℓ})
traverse f List.[]       = RaInst.pure List.[]
traverse f (x List.∷ xs) = RaInst.liftA2 List._∷_ (f x) (traverse f xs)

-- Total decode
decode : ∀{aℓ} {A : Type aℓ} {pℓ} {P : Json.Value → Type pℓ} → (v : Json.Value) → ((v' : Json.Value) → P v' → A) → (Σ (Json.IsArray v) λ (xs , _) → All P xs) → List A
decode v dec (_ , all) = map (λ (x , p) → dec x p) $′ All.toList all
