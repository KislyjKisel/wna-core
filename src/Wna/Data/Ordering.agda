{-# OPTIONS --without-K --safe #-}

module Wna.Data.Ordering where

open import Wna.Primitive

data Ordering : Type where
    less greater equal : Ordering

flip : Ordering → Ordering
flip less    = greater
flip equal   = equal
flip greater = less
