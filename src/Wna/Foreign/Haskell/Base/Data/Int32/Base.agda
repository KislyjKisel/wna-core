-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Int32.Base where

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
  Int32 : Type

{-# COMPILE GHC Int32 = type Data.Int.Int32 #-}


postulate

  -- Num
  _+_ : Int32 -> Int32 -> Int32
  _-_ : Int32 -> Int32 -> Int32
  _*_ : Int32 -> Int32 -> Int32
  _^_ : Int32 -> Int32 -> Int32
  negate : Int32 -> Int32
  abs : Int32 -> Int32
  fromℤ : ℤ -> Int32

  -- Enum
  succ : Int32 -> Int32
  pred : Int32 -> Int32

  -- Eq
  _==_ : Int32 -> Int32 -> Bool
  _/=_ : Int32 -> Int32 -> Bool

  -- Ord
  compare : Int32 -> Int32 -> Ordering
  _<_ : Int32 -> Int32 -> Bool
  _≤_ : Int32 -> Int32 -> Bool
  _>_ : Int32 -> Int32 -> Bool
  _≥_ : Int32 -> Int32 -> Bool
  _⊓_ : Int32 -> Int32 -> Int32
  _⊔_ : Int32 -> Int32 -> Int32

  -- Bounded
  minBound : Int32
  maxBound : Int32

  -- Integral
  _quot_ : Int32 -> Int32 -> Int32
  _rem_ : Int32 -> Int32 -> Int32
  _div_ : Int32 -> Int32 -> Int32
  _mod_ : Int32 -> Int32 -> Int32
  _quotRem_ : Int32 -> Int32 -> Pair Int32 Int32
  _divMod_ : Int32 -> Int32 -> Pair Int32 Int32
  toℤ : Int32 -> ℤ
  toFloat : Int32 -> Float

  -- Bits
  _xor_ : Int32 -> Int32 -> Int32
  _∙∣∙_ : Int32 -> Int32 -> Int32
  _∙&∙_ : Int32 -> Int32 -> Int32
  complement : Int32 -> Int32
  popCount : Int32 -> Int
  shift : Int32 -> Int -> Int32
  rotate : Int32 -> Int -> Int32

  -- FiniteBits
  bitSize : Int32 -> Int
  countLeadingZeros : Int32 -> Int
  countTrailingZeros : Int32 -> Int

  fromℕ : ℕ -> Int32


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


shiftL : Int32 -> ℕ -> Int32
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Int32 -> ℕ -> Int32
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Int32 -> ℕ -> Int32
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Int32 -> ℕ -> Int32
rotateR x n = rotate x (ℕ⇒-Int n)
