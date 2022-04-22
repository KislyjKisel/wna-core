{-# OPTIONS --without-K --safe #-}

module Wna.Primitive where

open import Agda.Primitive public
    using ()
    renaming (Setω to Typeω; Set to Type; _⊔_ to _ℓ⊔_; lsuc to ℓ↑)
