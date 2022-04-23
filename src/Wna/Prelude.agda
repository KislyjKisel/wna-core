{-# OPTIONS --without-K --safe #-}

module Wna.Prelude where

open import Wna.Primitive public

---- # Data

open import Data.Nat.Base public
    using (ℕ)


open import Data.Maybe.Base public
    using
    ( Maybe ; just ; nothing
    ; maybe ; maybe′ ; fromMaybe ; is-just ; is-nothing
    )

module Mb = Data.Maybe.Base


open import Data.Product public
    using
    ( Σ ; proj₁ ; proj₂
    ; ∃ ; ∄ ; ∃!
    ; _,_ ; _×_ ; _,′_ ; -,_
    ; curry ; uncurry ; curry′ ; uncurry′
    )

module Σ = Data.Product


open import Data.Sum.Base public
    using (_⊎_ ; inj₁ ; inj₂)

module ⊎ = Data.Sum.Base


open import Data.Bool.Base public
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


open import Data.String.Base public
    using (String)

module Str = Data.String.Base


open import Data.Fin.Base public
    using (Fin)

module Fin = Data.Fin.Base


open import Data.Sign.Base public
    using (Sign)

module Sign = Data.Sign.Base


open import Data.List.Base public
    using (List)

module List = Data.List.Base

pattern []  = List.[]
pattern _∷_ = List._∷_


open import Data.Vec.Base public
    using (Vec)

module Vec = Data.Vec.Base

pattern []  = Vec.[]
pattern _∷_ = Vec._∷_

---- # Function

open import Function.Base public
    using
    ( id ; const ; constᵣ ; flip
    ; _$_ ; _∘_ ; _∘₂_ ; _∣>_ ; case_return_of
    ; _$′_ ; _∘′_ ; _∘₂′_ ; _∣>′_ ; case_of_
    ; λ- ; $-
    ; _⟨_⟩_ ; _∋_ ; typeOf ; it
    ; _on₂_ ; _on_
    )

open import Function.Strict public
    using
    -- note: stdlib's _!∣>_ has no fixity declaration (_!∣>′_ has two, typo?)
    ( _$!_ ; _!∣>_ ; _!∣>′_
    )
