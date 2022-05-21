-- ! this module is generated automatically

{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Int.Base where

open import Data.Bool.Base using (Bool)
open import Data.Float.Base using (Float)
open import Data.Integer.Base using (ℤ; +_; -_)
open import Data.Nat.Base using (ℕ)
open import Foreign.Haskell.Pair using (Pair)
open import Wna.Foreign.Haskell.Base.Data.Ordering.Base using (Ordering)
open import Wna.Primitive
open import Data.List.Base using (List)
open import Data.Char.Base using (Char)

{-# FOREIGN GHC import Data.Int #-}
{-# FOREIGN GHC import Data.Bits #-}


postulate
  Int : Type

{-# COMPILE GHC Int = type Data.Int.Int #-}


postulate

  -- Num
  show : Int -> List Char

  -- Num
  _+_ : Int -> Int -> Int
  _-_ : Int -> Int -> Int
  _*_ : Int -> Int -> Int
  _^_ : Int -> Int -> Int
  negate : Int -> Int
  abs : Int -> Int
  fromℤ : ℤ -> Int

  -- Enum
  succ : Int -> Int
  pred : Int -> Int

  -- Eq
  _==_ : Int -> Int -> Bool
  _/=_ : Int -> Int -> Bool

  -- Ord
  compare : Int -> Int -> Ordering
  _<_ : Int -> Int -> Bool
  _≤_ : Int -> Int -> Bool
  _>_ : Int -> Int -> Bool
  _≥_ : Int -> Int -> Bool
  _⊓_ : Int -> Int -> Int
  _⊔_ : Int -> Int -> Int

  -- Bounded
  minBound : Int
  maxBound : Int

  -- Integral
  _quot_ : Int -> Int -> Int
  _rem_ : Int -> Int -> Int
  _div_ : Int -> Int -> Int
  _mod_ : Int -> Int -> Int
  _quotRem_ : Int -> Int -> Pair Int Int
  _divMod_ : Int -> Int -> Pair Int Int
  toℤ : Int -> ℤ
  toFloat : Int -> Float

  -- Bits
  _xor_ : Int -> Int -> Int
  _∙∣∙_ : Int -> Int -> Int
  _∙&∙_ : Int -> Int -> Int
  complement : Int -> Int
  popCount : Int -> Int
  shift : Int -> Int -> Int
  rotate : Int -> Int -> Int

  -- FiniteBits
  bitSize : Int -> Int
  countLeadingZeros : Int -> Int
  countTrailingZeros : Int -> Int

  fromℕ : ℕ -> Int


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


ℕ⇒+Int : ℕ → Int
ℕ⇒+Int n = fromℤ (+ n)

ℕ⇒-Int : ℕ → Int
ℕ⇒-Int n = fromℤ (- (+ n))

shiftL : Int -> ℕ -> Int
shiftL x n = shift x (ℕ⇒+Int n)

rotateL : Int -> ℕ -> Int
rotateL x n = rotate x (ℕ⇒+Int n)

shiftR : Int -> ℕ -> Int
shiftR x n = shift x (ℕ⇒-Int n)

rotateR : Int -> ℕ -> Int
rotateR x n = rotate x (ℕ⇒-Int n)
