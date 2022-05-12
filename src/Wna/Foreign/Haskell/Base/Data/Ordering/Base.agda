{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Ordering.Base where

open import Wna.Data.Ordering as Safe using ()
open import Wna.Primitive

data Ordering : Type where
    LT EQ GT : Ordering

{-# COMPILE GHC Ordering = data Prelude.Ordering (LT | EQ | GT) #-}

toForeign : Safe.Ordering → Ordering
toForeign Safe.less    = LT
toForeign Safe.equal   = EQ
toForeign Safe.greater = GT

fromForeign : Ordering → Safe.Ordering
fromForeign LT = Safe.less
fromForeign EQ = Safe.equal
fromForeign GT = Safe.greater
