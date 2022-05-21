{-# OPTIONS --without-K --safe #-}

module Wna.Data.List.Serialization.Json where

open import Data.Product                   using (_,_)
open import Function.Base                  using (case_of_; _$′_; _∘′_)
open import Relation.Nullary               using (yes; no)
open import Wna.Data.List.Base
open import Wna.Data.List.Bundles          using (foldable)
open import Wna.Monad.Except       as Ex   using ()
open import Wna.Monad.Identity     as Id   using ()
open import Wna.Primitive
open import Wna.Serialization.Json as Json using ()

json-encode : ∀{ℓ} {A : Type ℓ} ⦃ _ : Json.Encode A ⦄ → Json.Encode (List A)
json-encode = record { encode = Json.array ∘′ map Json.EncodeInstanced.encode }

json-decode : ∀{ℓ} {A : Type ℓ} ⦃ _ : Json.Decode A ⦄ → Json.Decode (List A)
json-decode {A = A} ⦃ A-decode ⦄ = record
    { decode = λ v → case (Json.IsArray? v) of λ where
        (no ¬p) → Ex.raise $′ liftℓ "Parsed value wasn't an array"
        (yes (xs , v≡axs)) → traverse (λ (liftℓ v') → A.decode v') (map liftℓ xs)
    }
    where
    module A = Json.Decode A-decode
    instance
        _ = Id.rawMonad
        _ = Ex.rawFunctor
        _ = Ex.rawApplicative
        _ = foldable
