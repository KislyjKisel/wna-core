{-# OPTIONS --without-K --safe #-}

module Wna.Data.Nat.Serialization.Json where

open import Data.Integer                          as ℤ    using ()
open import Data.Nat.Base                         as ℕ    using (ℕ)
open import Data.Product                                  using (_,_)
open import Function.Base                                 using (case_of_)
open import Relation.Nullary                              using (yes; no)
open import Wna.Data.Scientific.Base                      using (mkScientific)
open import Wna.Data.Scientific.Unnormalized.Base         using (mkScientificᵘ; normalize)
open import Wna.Monad.Except                      as Ex   using ()
open import Wna.Monad.Identity.Bundles            as Id   using ()
open import Wna.Primitive
open import Wna.Serialization.Json                as Json using ()

json-encode : Json.Encode ℕ
json-encode = record
    { encode = λ n → Json.number (mkScientificᵘ (ℤ.+ n) ℤ.0ℤ)
    }

json-decode : Json.Decode ℕ
json-decode = record
    { decode = λ v → case Json.IsNumber? v of λ where
        (no _)        → Ex.raise (liftℓ "parsed value wasn't a number")
        (yes (sᵘ , _)) → case normalize sᵘ of λ where
            (mkScientific m e _ _) → case ℤ.0ℤ ℤ.≤? e of λ where
                (no _)    → Ex.raise (liftℓ "parsed number wasn't integral")
                (yes e≥0) → case ℤ.0ℤ ℤ.≤? m of λ where
                    (no _)    → Ex.raise (liftℓ "parsed number was negative")
                    (yes m≥0) → Ex.pure (ℤ.∣ m ∣ ℕ.* (10 ℕ.^ ℤ.∣ e ∣))
    }
    where
    instance
        _ = Id.rawMonad
        _ = Ex.rawApplicative
