-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Word.Base where

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
  Word : Type

{-# COMPILE GHC Word = type Data.Word.Word #-}


postulate

  -- Num
  show : Word -> List Char

  -- Num
  _+_ : Word -> Word -> Word
  _-_ : Word -> Word -> Word
  _*_ : Word -> Word -> Word
  _^_ : Word -> Word -> Word
  negate : Word -> Word
  abs : Word -> Word
  fromℤ : ℤ -> Word

  -- Enum
  succ : Word -> Word
  pred : Word -> Word

  -- Eq
  _==_ : Word -> Word -> Bool
  _/=_ : Word -> Word -> Bool

  -- Ord
  compare : Word -> Word -> Ordering
  _<_ : Word -> Word -> Bool
  _≤_ : Word -> Word -> Bool
  _>_ : Word -> Word -> Bool
  _≥_ : Word -> Word -> Bool
  _⊓_ : Word -> Word -> Word
  _⊔_ : Word -> Word -> Word

  -- Bounded
  minBound : Word
  maxBound : Word

  -- Integral
  _quot_ : Word -> Word -> Word
  _rem_ : Word -> Word -> Word
  _div_ : Word -> Word -> Word
  _mod_ : Word -> Word -> Word
  _quotRem_ : Word -> Word -> Pair Word Word
  _divMod_ : Word -> Word -> Pair Word Word
  toℤ : Word -> ℤ
  toFloat : Word -> Float

  -- Bits
  _xor_ : Word -> Word -> Word
  _∙∣∙_ : Word -> Word -> Word
  _∙&∙_ : Word -> Word -> Word
  complement : Word -> Word
  popCount : Word -> Int
  shift : Word -> Int -> Word
  rotate : Word -> Int -> Word

  -- FiniteBits
  bitSize : Word -> Int
  countLeadingZeros : Word -> Int
  countTrailingZeros : Word -> Int

  fromℕ : ℕ -> Word


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


shiftL : Word -> ℕ -> Word
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Word -> ℕ -> Word
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Word -> ℕ -> Word
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Word -> ℕ -> Word
rotateR x n = rotate x (ℕ⇒-Int n)

postulate
  toℕ : Word -> ℕ

{-# COMPILE GHC toℕ = Prelude.toInteger #-}
