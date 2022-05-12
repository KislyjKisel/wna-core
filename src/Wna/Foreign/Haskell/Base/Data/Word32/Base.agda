-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Word32.Base where

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
  Word32 : Type

{-# COMPILE GHC Word32 = type Data.Word.Word32 #-}


postulate

  -- Num
  _+_ : Word32 -> Word32 -> Word32
  _-_ : Word32 -> Word32 -> Word32
  _*_ : Word32 -> Word32 -> Word32
  _^_ : Word32 -> Word32 -> Word32
  negate : Word32 -> Word32
  abs : Word32 -> Word32
  fromℤ : ℤ -> Word32

  -- Enum
  succ : Word32 -> Word32
  pred : Word32 -> Word32

  -- Eq
  _==_ : Word32 -> Word32 -> Bool
  _/=_ : Word32 -> Word32 -> Bool

  -- Ord
  compare : Word32 -> Word32 -> Ordering
  _<_ : Word32 -> Word32 -> Bool
  _≤_ : Word32 -> Word32 -> Bool
  _>_ : Word32 -> Word32 -> Bool
  _≥_ : Word32 -> Word32 -> Bool
  _⊓_ : Word32 -> Word32 -> Word32
  _⊔_ : Word32 -> Word32 -> Word32

  -- Bounded
  minBound : Word32
  maxBound : Word32

  -- Integral
  _quot_ : Word32 -> Word32 -> Word32
  _rem_ : Word32 -> Word32 -> Word32
  _div_ : Word32 -> Word32 -> Word32
  _mod_ : Word32 -> Word32 -> Word32
  _quotRem_ : Word32 -> Word32 -> Pair Word32 Word32
  _divMod_ : Word32 -> Word32 -> Pair Word32 Word32
  toℤ : Word32 -> ℤ
  toFloat : Word32 -> Float

  -- Bits
  _xor_ : Word32 -> Word32 -> Word32
  _∙∣∙_ : Word32 -> Word32 -> Word32
  _∙&∙_ : Word32 -> Word32 -> Word32
  complement : Word32 -> Word32
  popCount : Word32 -> Int
  shift : Word32 -> Int -> Word32
  rotate : Word32 -> Int -> Word32

  -- FiniteBits
  bitSize : Word32 -> Int
  countLeadingZeros : Word32 -> Int
  countTrailingZeros : Word32 -> Int

  fromℕ : ℕ -> Word32


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


shiftL : Word32 -> ℕ -> Word32
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Word32 -> ℕ -> Word32
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Word32 -> ℕ -> Word32
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Word32 -> ℕ -> Word32
rotateR x n = rotate x (ℕ⇒-Int n)

postulate
  toℕ : Word32 -> ℕ

{-# COMPILE GHC toℕ = Prelude.toInteger #-}
