{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Std where

open import Wna.Primitive public

---- # Data

open import Data.Nat public
    using  (ℕ)
    hiding (module ℕ)

module ℕ where
    open Data.Nat public
        hiding (ℕ)


open import Data.Integer public
    using  (ℤ)
    hiding (module ℤ)

module ℤ where
    open Data.Integer public
        hiding (ℤ)

open import Data.Float public
    using (Float)

module Float where
    open Data.Float public
        hiding (Float)


open import Data.Maybe public
    using
    ( Maybe ; just ; nothing
    ; maybe ; maybe′ ; fromMaybe ; is-just ; is-nothing
    )
    hiding (module Maybe)

module Maybe = Data.Maybe


open import Data.Product public
    using
    ( Σ ; proj₁ ; proj₂
    ; ∃ ; ∄ ; ∃!
    ; _,_ ; _×_ ; _,′_ ; -,_
    ; curry ; uncurry ; curry′ ; uncurry′
    )
    hiding (module Σ)

module Σ = Data.Product


open import Data.Sum public
    using (_⊎_ ; inj₁ ; inj₂)

module ⊎ = Data.Sum


open import Data.Bool public
    using (Bool; true; false; if_then_else_)


open import Data.Unit public
    using (⊤; tt)

open import Data.Unit.Polymorphic public
    using ()
    renaming (⊤ to ⊤′; tt to tt′)


open import Data.Empty public
    using (⊥; ⊥-elim)

open import Data.Empty public
    using ()
    renaming (⊥ to ⊥′; ⊥-elim to ⊥′-elim)


open import Data.String public
    using (String)

module String = Data.String


open import Data.Fin public
    using (Fin)
    hiding (module Fin)

module Fin = Data.Fin


open import Data.Sign public
    using (Sign)
    hiding (module Sign)

module Sign = Data.Sign


open import Data.List public
    using (List)
    hiding (module List)

module List = Data.List


open import Data.Vec public
    using (Vec)
    hiding (module Vec)

module Vec = Data.Vec

---- # Function

open import Function.Base public
    using
    ( id ; const ; constᵣ ; flip
    ; _$_ ; _∘_ ; _∘₂_ ; _|>_ ; case_return_of_
    ; _$′_ ; _∘′_ ; _∘₂′_ ; _|>′_ ; case_of_
    ; λ- ; _$-
    ; _⟨_⟩_ ; _∋_ ; typeOf ; it
    ; _on₂_ ; _on_
    )

open import Function.Strict public
    using
    -- note: stdlib's _!∣>_ has no fixity declaration (_!∣>′_ has two, typo?)
    ( _$!_ ; _!|>_ ; _!|>′_
    )

-- # Reasoning

open import Relation.Binary.PropositionalEquality public
    using ( _≡_ ; _≢_ ; _≗_ ; inspect )

module ≡ where
    open Relation.Binary.PropositionalEquality public
        hiding (_≡_; _≢_; _≗_)


open import Relation.Nullary public
    using
    ( ¬_
    ; Dec ; yes ; no
    )
