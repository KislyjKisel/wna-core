-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Word16.Base where

open import Data.Bool.Base using (Bool)
open import Data.Float.Base using (Float)
open import Data.Integer.Base using (ℤ; +_; -_)
open import Data.Nat.Base using (ℕ)
open import Foreign.Haskell.Pair using (Pair)
open import Wna.Foreign.Haskell.Base.Data.Ordering.Base using (Ordering)
open import Wna.Primitive
open import Wna.Foreign.Haskell.Base.Data.Int.Base using (Int; ℕ⇒+Int; ℕ⇒-Int)

{-# FOREIGN GHC import Data.Word #-}
{-# FOREIGN GHC import Data.Bits #-}


postulate
  Word16 : Type

{-# COMPILE GHC Word16 = type Data.Word.Word16 #-}


postulate

  -- Num
  _+_ : Word16 -> Word16 -> Word16
  _-_ : Word16 -> Word16 -> Word16
  _*_ : Word16 -> Word16 -> Word16
  _^_ : Word16 -> Word16 -> Word16
  negate : Word16 -> Word16
  abs : Word16 -> Word16
  fromℤ : ℤ -> Word16

  -- Enum
  succ : Word16 -> Word16
  pred : Word16 -> Word16

  -- Eq
  _==_ : Word16 -> Word16 -> Bool
  _/=_ : Word16 -> Word16 -> Bool

  -- Ord
  compare : Word16 -> Word16 -> Ordering
  _<_ : Word16 -> Word16 -> Bool
  _≤_ : Word16 -> Word16 -> Bool
  _>_ : Word16 -> Word16 -> Bool
  _≥_ : Word16 -> Word16 -> Bool
  _⊓_ : Word16 -> Word16 -> Word16
  _⊔_ : Word16 -> Word16 -> Word16

  -- Bounded
  minBound : Word16
  maxBound : Word16

  -- Integral
  _quot_ : Word16 -> Word16 -> Word16
  _rem_ : Word16 -> Word16 -> Word16
  _div_ : Word16 -> Word16 -> Word16
  _mod_ : Word16 -> Word16 -> Word16
  _quotRem_ : Word16 -> Word16 -> Pair Word16 Word16
  _divMod_ : Word16 -> Word16 -> Pair Word16 Word16
  toℤ : Word16 -> ℤ
  toFloat : Word16 -> Float

  -- Bits
  _xor_ : Word16 -> Word16 -> Word16
  _∙∣∙_ : Word16 -> Word16 -> Word16
  _∙&∙_ : Word16 -> Word16 -> Word16
  complement : Word16 -> Word16
  popCount : Word16 -> Int
  shift : Word16 -> Int -> Word16
  rotate : Word16 -> Int -> Word16

  -- FiniteBits
  bitSize : Word16 -> Int
  countLeadingZeros : Word16 -> Int
  countTrailingZeros : Word16 -> Int

  fromℕ : ℕ -> Word16


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


shiftL : Word16 -> ℕ -> Word16
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Word16 -> ℕ -> Word16
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Word16 -> ℕ -> Word16
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Word16 -> ℕ -> Word16
rotateR x n = rotate x (ℕ⇒-Int n)

postulate
  toℕ : Word16 -> ℕ

{-# COMPILE GHC toℕ = Prelude.toInteger #-}
