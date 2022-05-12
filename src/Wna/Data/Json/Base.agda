{-# OPTIONS --without-K --safe #-}

module Wna.Data.Json.Base where

open import Data.String.Properties as Sp using ()
open import Data.String.Base             using (String)
open import Data.List.Base               using (List)
open import Data.Bool.Base               using (Bool)
open import Wna.Data.Scientific.Base     using (Scientific)
open import Wna.Primitive

open import Data.Tree.AVL.Map Sp.<-strictTotalOrder-≈
    using (Map)

data Json : Type where
    object : Map Json   → Json
    array  : List Json  → Json
    string : String     → Json
    number : Scientific → Json
    bool   : Bool       → Json
    null   :              Json
