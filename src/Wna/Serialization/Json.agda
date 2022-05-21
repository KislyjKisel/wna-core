{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Json where

open import Wna.Serialization.Json.Value           public
open import Wna.Serialization.Json.Value.Predicate public

open import Wna.Serialization.Json.Decode public
    renaming (module Instanced to DecodeInstanced)

open import Wna.Serialization.Json.Encode public
    renaming (module Instanced to EncodeInstanced)
