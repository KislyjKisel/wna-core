-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Int16.Base where

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
  Int16 : Type

{-# COMPILE GHC Int16 = type Data.Int.Int16 #-}


postulate

  -- Num
  _+_ : Int16 -> Int16 -> Int16
  _-_ : Int16 -> Int16 -> Int16
  _*_ : Int16 -> Int16 -> Int16
  _^_ : Int16 -> Int16 -> Int16
  negate : Int16 -> Int16
  abs : Int16 -> Int16
  fromℤ : ℤ -> Int16

  -- Enum
  succ : Int16 -> Int16
  pred : Int16 -> Int16

  -- Eq
  _==_ : Int16 -> Int16 -> Bool
  _/=_ : Int16 -> Int16 -> Bool

  -- Ord
  compare : Int16 -> Int16 -> Ordering
  _<_ : Int16 -> Int16 -> Bool
  _≤_ : Int16 -> Int16 -> Bool
  _>_ : Int16 -> Int16 -> Bool
  _≥_ : Int16 -> Int16 -> Bool
  _⊓_ : Int16 -> Int16 -> Int16
  _⊔_ : Int16 -> Int16 -> Int16

  -- Bounded
  minBound : Int16
  maxBound : Int16

  -- Integral
  _quot_ : Int16 -> Int16 -> Int16
  _rem_ : Int16 -> Int16 -> Int16
  _div_ : Int16 -> Int16 -> Int16
  _mod_ : Int16 -> Int16 -> Int16
  _quotRem_ : Int16 -> Int16 -> Pair Int16 Int16
  _divMod_ : Int16 -> Int16 -> Pair Int16 Int16
  toℤ : Int16 -> ℤ
  toFloat : Int16 -> Float

  -- Bits
  _xor_ : Int16 -> Int16 -> Int16
  _∙∣∙_ : Int16 -> Int16 -> Int16
  _∙&∙_ : Int16 -> Int16 -> Int16
  complement : Int16 -> Int16
  popCount : Int16 -> Int
  shift : Int16 -> Int -> Int16
  rotate : Int16 -> Int -> Int16

  -- FiniteBits
  bitSize : Int16 -> Int
  countLeadingZeros : Int16 -> Int
  countTrailingZeros : Int16 -> Int

  fromℕ : ℕ -> Int16


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


shiftL : Int16 -> ℕ -> Int16
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Int16 -> ℕ -> Int16
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Int16 -> ℕ -> Int16
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Int16 -> ℕ -> Int16
rotateR x n = rotate x (ℕ⇒-Int n)
