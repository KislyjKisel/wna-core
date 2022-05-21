-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Word8.Base where

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
  Word8 : Type

{-# COMPILE GHC Word8 = type Data.Word.Word8 #-}


postulate

  -- Num
  show : Word8 -> List Char

  -- Num
  _+_ : Word8 -> Word8 -> Word8
  _-_ : Word8 -> Word8 -> Word8
  _*_ : Word8 -> Word8 -> Word8
  _^_ : Word8 -> Word8 -> Word8
  negate : Word8 -> Word8
  abs : Word8 -> Word8
  fromℤ : ℤ -> Word8

  -- Enum
  succ : Word8 -> Word8
  pred : Word8 -> Word8

  -- Eq
  _==_ : Word8 -> Word8 -> Bool
  _/=_ : Word8 -> Word8 -> Bool

  -- Ord
  compare : Word8 -> Word8 -> Ordering
  _<_ : Word8 -> Word8 -> Bool
  _≤_ : Word8 -> Word8 -> Bool
  _>_ : Word8 -> Word8 -> Bool
  _≥_ : Word8 -> Word8 -> Bool
  _⊓_ : Word8 -> Word8 -> Word8
  _⊔_ : Word8 -> Word8 -> Word8

  -- Bounded
  minBound : Word8
  maxBound : Word8

  -- Integral
  _quot_ : Word8 -> Word8 -> Word8
  _rem_ : Word8 -> Word8 -> Word8
  _div_ : Word8 -> Word8 -> Word8
  _mod_ : Word8 -> Word8 -> Word8
  _quotRem_ : Word8 -> Word8 -> Pair Word8 Word8
  _divMod_ : Word8 -> Word8 -> Pair Word8 Word8
  toℤ : Word8 -> ℤ
  toFloat : Word8 -> Float

  -- Bits
  _xor_ : Word8 -> Word8 -> Word8
  _∙∣∙_ : Word8 -> Word8 -> Word8
  _∙&∙_ : Word8 -> Word8 -> Word8
  complement : Word8 -> Word8
  popCount : Word8 -> Int
  shift : Word8 -> Int -> Word8
  rotate : Word8 -> Int -> Word8

  -- FiniteBits
  bitSize : Word8 -> Int
  countLeadingZeros : Word8 -> Int
  countTrailingZeros : Word8 -> Int

  fromℕ : ℕ -> Word8


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


shiftL : Word8 -> ℕ -> Word8
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Word8 -> ℕ -> Word8
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Word8 -> ℕ -> Word8
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Word8 -> ℕ -> Word8
rotateR x n = rotate x (ℕ⇒-Int n)

postulate
  toℕ : Word8 -> ℕ

{-# COMPILE GHC toℕ = Prelude.toInteger #-}
