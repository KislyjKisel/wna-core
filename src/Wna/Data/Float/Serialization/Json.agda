{-# OPTIONS --without-K --safe #-}

module Wna.Data.Float.Serialization.Json where

open import Data.Float.Base                               using (Float; decode)
open import Data.Maybe.Base                               using (just; nothing)
open import Data.Nat.Properties                   as ℕ    using ()
open import Data.Product                                  using (proj₁; _×_; _,_)
open import Function.Base                                 using (case_of_; _$_)
open import Relation.Binary.Definitions                   using (tri<; tri≈; tri>)
open import Relation.Nullary                              using (yes; no)
open import Wna.Data.Integer.Base                 as ℤ    using (ℤ)
open import Wna.Data.Integer.Properties           as ℤ    using ()
open import Wna.Data.Nat.Base                     as ℕ    using (ℕ)
open import Wna.Data.Scientific.Unnormalized.Base as Sci  using ()
open import Wna.Monad.Except                      as Ex   using ()
open import Wna.Monad.Identity                    as Id   using ()
open import Wna.Primitive
open import Wna.Serialization.Json                as Json using ()

json-decode : Json.Decode Float
json-decode = record
    { decode = λ v → case (Json.IsNumber? v) of λ where
        (yes p) → Ex.pure $ Sci.toFloat $ proj₁ p
        (no ¬p) → Ex.raise $ liftℓ "Parsed value wasn't numeric"
    }

json-encode : Json.Encode Float
json-encode = record
    { encode = λ x → Json.number $ case decode x of λ where
        nothing          → Sci.mkScientificᵘ ℤ.0ℤ ℤ.-1ℤ
        (just (m₂ , e₂)) → case e₂ ℤ.≤? ℤ.0ℤ of λ where
            (yes e≤0) → Sci.mkScientificᵘ (m₂ ℤ.* ℤ.+ (5 ℕ.^ ℤ.∣ e₂ ∣)) e₂
            (no e>0)  → case ℤ.<-cmp m₂ ℤ.0ℤ of λ where
                (tri≈ ≮ ≈ ≯) → Sci.mkScientificᵘ ℤ.0ℤ ℤ.0ℤ
                (tri> ≮ ≉ >) → let (m₁₀ , e₁₀) = aux ℤ.∣ m₂ ∣ ⦃ ℕ.≢-nonZero (ℤ.i≢0⇒∣i∣≢0 m₂ ≉) ⦄ ℤ.∣ e₂ ∣ in Sci.mkScientificᵘ (ℤ.+ m₁₀) e₁₀
                (tri< < ≉ ≯) → let (m₁₀ , e₁₀) = aux ℤ.∣ m₂ ∣ ⦃ ℕ.≢-nonZero (ℤ.i≢0⇒∣i∣≢0 m₂ ≉) ⦄ ℤ.∣ e₂ ∣ in Sci.mkScientificᵘ (ℤ.-[1+ ℕ.pred m₁₀ ]) e₁₀
    }
    where
    aux : (m₂ : ℕ) → ⦃ _ : ℕ.NonZero m₂ ⦄ → ℕ → ℕ × ℤ
    aux m₂ e₂ with ℕ.log m₂ {d = 5} (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
    ... | (ℕlog₅m , rem , _) with e₂ ℕ.≤? ℕlog₅m
    ... | (yes logm≥e) = rem ℕ.* (5 ℕ.^ (ℕlog₅m ℕ.∸ e₂)) , ℤ.+ e₂
    ... | (no  logm<e) = rem ℕ.* (2 ℕ.^ (e₂ ℕ.∸ ℕlog₅m)) , ℤ.+ (e₂ ℕ.∸ ℕlog₅m)
