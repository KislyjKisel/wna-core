{-# OPTIONS --without-K --safe #-}

module Wna.Primitive where

open import Agda.Primitive public
    using    (Level)
    renaming
        ( Setω   to Typeω
        ; Set    to Type
        ; lzero  to 0ℓ
        ; lsuc   to ℓ↑
        ; _⊔_    to _ℓ⊔_
        )
