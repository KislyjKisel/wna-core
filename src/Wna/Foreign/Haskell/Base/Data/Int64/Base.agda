-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Int64.Base where

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

{-# FOREIGN GHC import Data.Int #-}
{-# FOREIGN GHC import Data.Bits #-}


postulate
  Int64 : Type

{-# COMPILE GHC Int64 = type Data.Int.Int64 #-}


postulate

  -- Num
  show : Int64 -> List Char

  -- Num
  _+_ : Int64 -> Int64 -> Int64
  _-_ : Int64 -> Int64 -> Int64
  _*_ : Int64 -> Int64 -> Int64
  _^_ : Int64 -> Int64 -> Int64
  negate : Int64 -> Int64
  abs : Int64 -> Int64
  fromℤ : ℤ -> Int64

  -- Enum
  succ : Int64 -> Int64
  pred : Int64 -> Int64

  -- Eq
  _==_ : Int64 -> Int64 -> Bool
  _/=_ : Int64 -> Int64 -> Bool

  -- Ord
  compare : Int64 -> Int64 -> Ordering
  _<_ : Int64 -> Int64 -> Bool
  _≤_ : Int64 -> Int64 -> Bool
  _>_ : Int64 -> Int64 -> Bool
  _≥_ : Int64 -> Int64 -> Bool
  _⊓_ : Int64 -> Int64 -> Int64
  _⊔_ : Int64 -> Int64 -> Int64

  -- Bounded
  minBound : Int64
  maxBound : Int64

  -- Integral
  _quot_ : Int64 -> Int64 -> Int64
  _rem_ : Int64 -> Int64 -> Int64
  _div_ : Int64 -> Int64 -> Int64
  _mod_ : Int64 -> Int64 -> Int64
  _quotRem_ : Int64 -> Int64 -> Pair Int64 Int64
  _divMod_ : Int64 -> Int64 -> Pair Int64 Int64
  toℤ : Int64 -> ℤ
  toFloat : Int64 -> Float

  -- Bits
  _xor_ : Int64 -> Int64 -> Int64
  _∙∣∙_ : Int64 -> Int64 -> Int64
  _∙&∙_ : Int64 -> Int64 -> Int64
  complement : Int64 -> Int64
  popCount : Int64 -> Int
  shift : Int64 -> Int -> Int64
  rotate : Int64 -> Int -> Int64

  -- FiniteBits
  bitSize : Int64 -> Int
  countLeadingZeros : Int64 -> Int
  countTrailingZeros : Int64 -> Int

  fromℕ : ℕ -> Int64


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


shiftL : Int64 -> ℕ -> Int64
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Int64 -> ℕ -> Int64
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Int64 -> ℕ -> Int64
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Int64 -> ℕ -> Int64
rotateR x n = rotate x (ℕ⇒-Int n)
