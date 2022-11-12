{-# OPTIONS --without-K --safe #-}

module Wna.Serialization.Json.Value.Relation.Unary where

open import Wna.Serialization.Json.Value
open import Data.Product                                using (∃-syntax; proj₂; _,_)
open import Data.String.Properties                as Sp using ()
open import Relation.Binary.PropositionalEquality as ≡  using (refl; _≡_)
open import Relation.Nullary                            using (Dec; yes; no)
open import Wna.Primitive

IsObject : Value → Type
IsObject v = ∃[ x ] v ≡ object x

IsObject? : (v : Value) → Dec (IsObject v)
IsObject? (object x) = yes (x , refl)
IsObject? (array  x) = no λ ()
IsObject? (string x) = no λ ()
IsObject? (number x) = no λ ()
IsObject? (bool   x) = no λ ()
IsObject?  null      = no λ ()

IsArray : Value → Type
IsArray v = ∃[ x ] v ≡ array x

IsArray? : (v : Value) → Dec (IsArray v)
IsArray? (object x) = no λ ()
IsArray? (array  x) = yes (x , refl)
IsArray? (string x) = no λ ()
IsArray? (number x) = no λ ()
IsArray? (bool   x) = no λ ()
IsArray?  null      = no λ ()

IsString : Value → Type
IsString v = ∃[ x ] v ≡ string x

IsString? : (v : Value) → Dec (IsString v)
IsString? (object x) = no λ ()
IsString? (array  x) = no λ ()
IsString? (string x) = yes (x , refl)
IsString? (number x) = no λ ()
IsString? (bool   x) = no λ ()
IsString?  null      = no λ ()

IsNumber : Value → Type
IsNumber v = ∃[ x ] v ≡ number x

IsNumber? : (v : Value) → Dec (IsNumber v)
IsNumber? (object x) = no λ ()
IsNumber? (array  x) = no λ ()
IsNumber? (string x) = no λ ()
IsNumber? (number x) = yes (x , refl)
IsNumber? (bool   x) = no λ ()
IsNumber?  null      = no λ ()

IsBool : Value → Type
IsBool v = ∃[ x ] v ≡ bool x

IsBool? : (v : Value) → Dec (IsBool v)
IsBool? (object x) = no λ ()
IsBool? (array  x) = no λ ()
IsBool? (string x) = no λ ()
IsBool? (number x) = no λ ()
IsBool? (bool   x) = yes (x , refl)
IsBool?  null      = no λ ()

IsNull : Value → Type
IsNull = _≡ null

IsNull? : (v : Value) → Dec (IsNull v)
IsNull? (object x) = no λ ()
IsNull? (array  x) = no λ ()
IsNull? (string x) = no λ ()
IsNull? (number x) = no λ ()
IsNull? (bool   x) = no λ ()
IsNull?  null      = yes refl
