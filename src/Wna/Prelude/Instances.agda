{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Instances where

import Wna.Data.Float.Bundles as Float
import Wna.Data.List.Bundles  as List
import Wna.Data.Nat.Bundles   as ℕ
import Wna.Data.Vec.Bundles   as Vec

-- ([A-Za-z\-ℕℤ]+) :.*\n.*\n  ->  ?-$1 = ?.$1

instance
    ℕ-add            = ℕ.add
    ℕ-subtract       = ℕ.subtract
    ℕ-multiply       = ℕ.multiply
    ℕ-square         = ℕ.square
    ℕ-power          = ℕ.power
    ℕ-join           = ℕ.join
    ℕ-meet           = ℕ.meet
    ℕ-rawEquality    = ℕ.rawEquality
    ℕ-rawStrictOrder = ℕ.rawStrictOrder
    ℕ-rawOrder       = ℕ.rawOrder
    ℕ-decStrictOrder = ℕ.decStrictOrder
    ℕ-decOrder       = ℕ.decOrder

    Float-negate         = Float.negate
    Float-add            = Float.add
    Float-subtract       = Float.subtract
    Float-multiply       = Float.multiply
    Float-divide         = Float.divide
    Float-square         = Float.square
    Float-reciprocal     = Float.reciprocal
    Float-power          = Float.power
    Float-exponential    = Float.exponential
    Float-absolute       = Float.absolute
    Float-join           = Float.join
    Float-meet           = Float.meet
    Float-rawStrictOrder = Float.rawStrictOrder
    Float-rawOrder       = Float.rawOrder
    Float-cast-fromℕ     = Float.cast-fromℕ
    Float-cast-fromℤ     = Float.cast-fromℤ

    List-foldable = List.foldable
    Vec-foldable  = Vec.foldable
