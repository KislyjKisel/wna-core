{-# OPTIONS --without-K --safe #-}

module Wna.Data.Vec.Serialization.Json where

open import Data.List.Base                        as List using ()
open import Data.Nat                              as ℕ    using ()
open import Data.Product                                  using (_,_)
open import Function.Base                                 using (case_of_; _$′_; _∘′_)
open import Relation.Binary.PropositionalEquality as ≡    using ()
open import Relation.Nullary                              using (yes; no)
open import Wna.Data.Vec.Base                     as Vec  using (Vec)
open import Wna.Monad.Except                      as Ex   using ()
open import Wna.Monad.Identity.Bundles            as Id   using ()
open import Wna.Primitive
open import Wna.Serialization.Json                as Json using ()

json-encode : ∀{ℓ} {A : Type ℓ} ⦃ _ : Json.Encode A ⦄ → ∀{n} → Json.Encode (Vec A n)
json-encode = record
    { encode = Json.array ∘′ Vec.toList ∘′ Vec.map Json.EncodeInstanced.encode
    }

json-decode : ∀{ℓ} {A : Type ℓ} ⦃ _ : Json.Decode A ⦄ → ∀{n} → Json.Decode (Vec A n)
json-decode ⦃ A-decode ⦄ {n} = record
    { decode = λ v → case Json.IsArray? v of λ where
        (no  _)       → Ex.raise $′ liftℓ "parsed value wasn't an array"
        (yes (a , _)) → case List.length a ℕ.≟ n of λ where
            (no  _) → Ex.raise $′ liftℓ "array length mismatch"
            (yes p) → Vec.traverse (A.decode ∘′ unliftℓ) $′ Vec.map liftℓ $′
                        ≡.subst (Vec _) p $′ Vec.fromList a
    }
    where
    module A = Json.Decode A-decode
    instance
        _ = Id.rawMonad
        _ = Ex.rawApplicative
