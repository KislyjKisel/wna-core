{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Json.Value where

open import Data.Bool.Base                              using (Bool)
open import Data.List.Base                              using (List)
open import Data.String.Base                            using (String)
open import Data.String.Properties                as Sp using ()
open import Wna.Data.Scientific.Unnormalized.Base       using (Scientificᵘ₁₀)
open import Wna.Primitive

open import Data.Tree.AVL.Map Sp.<-strictTotalOrder-≈
    using (Map)

data Value : Type where
    object : Map Value     → Value
    array  : List Value    → Value
    string : String        → Value
    number : Scientificᵘ₁₀ → Value
    bool   : Bool          → Value
    null   :                 Value
