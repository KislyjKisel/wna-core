{-# OPTIONS --without-K --safe #-}

module Wna.Data.Integer.Properties where

open import Wna.Data.Integer.Base
open import Relation.Binary.PropositionalEquality as ≡ using (_≢_)
open import Function.Base using (_$′_)

open import Data.Integer.Properties public

i≢0⇒∣i∣≢0 : ∀ i → i ≢ (+ 0) → ∣ i ∣ ≢ 0
i≢0⇒∣i∣≢0 (+_ n)     ≉ n≡0 = ≉ $′ ≡.cong +_ n≡0
i≢0⇒∣i∣≢0 (-[1+ n ]) ≉ ()
