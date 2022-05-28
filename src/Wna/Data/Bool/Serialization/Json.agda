{-# OPTIONS --without-K --safe #-}

module Wna.Data.Bool.Serialization.Json where

open import Data.Bool.Base                   using (Bool)
open import Data.Product                     using (_,_)
open import Function.Base                    using (case_of_; _$′_)
open import Relation.Nullary                 using (yes; no)
open import Wna.Monad.Except.Base  as Except using ()
open import Wna.Primitive
open import Wna.Serialization.Json as Json   using ()

json-encode : Json.Encode Bool
json-encode = record
    { encode = Json.bool
    }

json-decode : Json.Decode Bool
json-decode = record
    { decode = λ v → case Json.IsBool? v of λ where
        (yes (x , _)) → Except.pure x
        (no _)        → Except.raise $′ liftℓ "parsed value wasn't bool" 
    }
