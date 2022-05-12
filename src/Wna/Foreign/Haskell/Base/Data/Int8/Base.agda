-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Int8.Base where

open import Data.Bool.Base using (Bool)
open import Data.Float.Base using (Float)
open import Data.Integer.Base using (ℤ; +_; -_)
open import Data.Nat.Base using (ℕ)
open import Foreign.Haskell.Pair using (Pair)
open import Wna.Foreign.Haskell.Base.Data.Ordering.Base using (Ordering)
open import Wna.Primitive
open import Wna.Foreign.Haskell.Base.Data.Int.Base using (Int; ℕ⇒+Int; ℕ⇒-Int)

{-# FOREIGN GHC import Data.Int #-}
{-# FOREIGN GHC import Data.Bits #-}


postulate
  Int8 : Type

{-# COMPILE GHC Int8 = type Data.Int.Int8 #-}


postulate

  -- Num
  _+_ : Int8 -> Int8 -> Int8
  _-_ : Int8 -> Int8 -> Int8
  _*_ : Int8 -> Int8 -> Int8
  _^_ : Int8 -> Int8 -> Int8
  negate : Int8 -> Int8
  abs : Int8 -> Int8
  fromℤ : ℤ -> Int8

  -- Enum
  succ : Int8 -> Int8
  pred : Int8 -> Int8

  -- Eq
  _==_ : Int8 -> Int8 -> Bool
  _/=_ : Int8 -> Int8 -> Bool

  -- Ord
  compare : Int8 -> Int8 -> Ordering
  _<_ : Int8 -> Int8 -> Bool
  _≤_ : Int8 -> Int8 -> Bool
  _>_ : Int8 -> Int8 -> Bool
  _≥_ : Int8 -> Int8 -> Bool
  _⊓_ : Int8 -> Int8 -> Int8
  _⊔_ : Int8 -> Int8 -> Int8

  -- Bounded
  minBound : Int8
  maxBound : Int8

  -- Integral
  _quot_ : Int8 -> Int8 -> Int8
  _rem_ : Int8 -> Int8 -> Int8
  _div_ : Int8 -> Int8 -> Int8
  _mod_ : Int8 -> Int8 -> Int8
  _quotRem_ : Int8 -> Int8 -> Pair Int8 Int8
  _divMod_ : Int8 -> Int8 -> Pair Int8 Int8
  toℤ : Int8 -> ℤ
  toFloat : Int8 -> Float

  -- Bits
  _xor_ : Int8 -> Int8 -> Int8
  _∙∣∙_ : Int8 -> Int8 -> Int8
  _∙&∙_ : Int8 -> Int8 -> Int8
  complement : Int8 -> Int8
  popCount : Int8 -> Int
  shift : Int8 -> Int -> Int8
  rotate : Int8 -> Int -> Int8

  -- FiniteBits
  bitSize : Int8 -> Int
  countLeadingZeros : Int8 -> Int
  countTrailingZeros : Int8 -> Int

  fromℕ : ℕ -> Int8


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


shiftL : Int8 -> ℕ -> Int8
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Int8 -> ℕ -> Int8
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Int8 -> ℕ -> Int8
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Int8 -> ℕ -> Int8
rotateR x n = rotate x (ℕ⇒-Int n)
