{-# OPTIONS --without-K --safe #-}

module Wna.Data.Float.Base where

open import Data.Bool.Base using (if_then_else_)

open import Data.Float.Base public

infixl 6 _∨_
infixl 7 _∧_
infix  7 1/_
infix  8 _²

_² : Float → Float
x ² = x * x

1/_ : Float → Float
1/ x = 1.0 ÷ x

_∨_ : Float → Float → Float
x ∨ y = if x <ᵇ y then y else x

_∧_ : Float → Float → Float
x ∧ y = if x ≤ᵇ y then x else y

abs : Float → Float
abs x = if x <ᵇ 0.0 then - x else x

sin² : Float → Float
sin² x = let sx = sin x in sx * sx

cos² : Float → Float
cos² x = let cx = cos x in cx * cx
