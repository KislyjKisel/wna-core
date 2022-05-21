-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Word64.Base where

open import Data.Bool.Base using (Bool)
open import Data.Float.Base using (Float)
open import Data.Integer.Base using (ℤ; +_; -_)
open import Data.Nat.Base using (ℕ)
open import Foreign.Haskell.Pair using (Pair)
open import Wna.Foreign.Haskell.Base.Data.Ordering.Base using (Ordering)
open import Wna.Primitive
open import Data.List.Base using (List)
open import Data.Char.Base using (Char)
open import Wna.Foreign.Haskell.Base.Data.Int.Base using (Int; ℕ⇒+Int; ℕ⇒-Int)

{-# FOREIGN GHC import Data.Word #-}
{-# FOREIGN GHC import Data.Bits #-}


postulate
  Word64 : Type

{-# COMPILE GHC Word64 = type Data.Word.Word64 #-}


postulate

  -- Num
  show : Word64 -> List Char

  -- Num
  _+_ : Word64 -> Word64 -> Word64
  _-_ : Word64 -> Word64 -> Word64
  _*_ : Word64 -> Word64 -> Word64
  _^_ : Word64 -> Word64 -> Word64
  negate : Word64 -> Word64
  abs : Word64 -> Word64
  fromℤ : ℤ -> Word64

  -- Enum
  succ : Word64 -> Word64
  pred : Word64 -> Word64

  -- Eq
  _==_ : Word64 -> Word64 -> Bool
  _/=_ : Word64 -> Word64 -> Bool

  -- Ord
  compare : Word64 -> Word64 -> Ordering
  _<_ : Word64 -> Word64 -> Bool
  _≤_ : Word64 -> Word64 -> Bool
  _>_ : Word64 -> Word64 -> Bool
  _≥_ : Word64 -> Word64 -> Bool
  _⊓_ : Word64 -> Word64 -> Word64
  _⊔_ : Word64 -> Word64 -> Word64

  -- Bounded
  minBound : Word64
  maxBound : Word64

  -- Integral
  _quot_ : Word64 -> Word64 -> Word64
  _rem_ : Word64 -> Word64 -> Word64
  _div_ : Word64 -> Word64 -> Word64
  _mod_ : Word64 -> Word64 -> Word64
  _quotRem_ : Word64 -> Word64 -> Pair Word64 Word64
  _divMod_ : Word64 -> Word64 -> Pair Word64 Word64
  toℤ : Word64 -> ℤ
  toFloat : Word64 -> Float

  -- Bits
  _xor_ : Word64 -> Word64 -> Word64
  _∙∣∙_ : Word64 -> Word64 -> Word64
  _∙&∙_ : Word64 -> Word64 -> Word64
  complement : Word64 -> Word64
  popCount : Word64 -> Int
  shift : Word64 -> Int -> Word64
  rotate : Word64 -> Int -> Word64

  -- FiniteBits
  bitSize : Word64 -> Int
  countLeadingZeros : Word64 -> Int
  countTrailingZeros : Word64 -> Int

  fromℕ : ℕ -> Word64


-- Num
{-# COMPILE GHC show = Prelude.show #-}

-- Num
{-# COMPILE GHC _+_ = (Prelude.+) #-}
{-# COMPILE GHC _-_ = (Prelude.-) #-}
{-# COMPILE GHC _*_ = (Prelude.*) #-}
{-# COMPILE GHC _^_ = (Prelude.^) #-}
{-# COMPILE GHC negate = Prelude.negate #-}
{-# COMPILE GHC abs = Prelude.abs #-}
{-# COMPILE GHC fromℤ = Prelude.fromInteger #-}

-- Enum
{-# COMPILE GHC succ = Prelude.succ #-}
{-# COMPILE GHC pred = Prelude.pred #-}

-- Eq
{-# COMPILE GHC _==_ = (Prelude.==) #-}
{-# COMPILE GHC _/=_ = (Prelude./=) #-}

-- Ord
{-# COMPILE GHC compare = Prelude.compare #-}
{-# COMPILE GHC _<_ = (Prelude.<) #-}
{-# COMPILE GHC _≤_ = (Prelude.<=) #-}
{-# COMPILE GHC _>_ = (Prelude.>) #-}
{-# COMPILE GHC _≥_ = (Prelude.>=) #-}
{-# COMPILE GHC _⊓_ = Prelude.min #-}
{-# COMPILE GHC _⊔_ = Prelude.max #-}

-- Bounded
{-# COMPILE GHC minBound = Prelude.minBound #-}
{-# COMPILE GHC maxBound = Prelude.maxBound #-}

-- Integral
{-# COMPILE GHC _quot_ = Prelude.quot #-}
{-# COMPILE GHC _rem_ = Prelude.rem #-}
{-# COMPILE GHC _div_ = Prelude.div #-}
{-# COMPILE GHC _mod_ = Prelude.mod #-}
{-# COMPILE GHC _quotRem_ = Prelude.quotRem #-}
{-# COMPILE GHC _divMod_ = Prelude.divMod #-}
{-# COMPILE GHC toℤ = Prelude.toInteger #-}
{-# COMPILE GHC toFloat = Prelude.fromIntegral #-}

-- Bits
{-# COMPILE GHC _xor_ = Data.Bits.xor #-}
{-# COMPILE GHC _∙∣∙_ = (Data.Bits..|.) #-}
{-# COMPILE GHC _∙&∙_ = (Data.Bits..&.) #-}
{-# COMPILE GHC complement = Data.Bits.complement #-}
{-# COMPILE GHC popCount = Data.Bits.popCount #-}
{-# COMPILE GHC shift = Data.Bits.shift #-}
{-# COMPILE GHC rotate = Data.Bits.rotate #-}

-- FiniteBits
{-# COMPILE GHC bitSize = Data.Bits.finiteBitSize #-}
{-# COMPILE GHC countLeadingZeros = Data.Bits.countLeadingZeros #-}
{-# COMPILE GHC countTrailingZeros = Data.Bits.countTrailingZeros #-}

{-# COMPILE GHC fromℕ = Prelude.fromInteger #-}


shiftL : Word64 -> ℕ -> Word64
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Word64 -> ℕ -> Word64
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Word64 -> ℕ -> Word64
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Word64 -> ℕ -> Word64
rotateR x n = rotate x (ℕ⇒-Int n)

postulate
  toℕ : Word64 -> ℕ

{-# COMPILE GHC toℕ = Prelude.toInteger #-}
