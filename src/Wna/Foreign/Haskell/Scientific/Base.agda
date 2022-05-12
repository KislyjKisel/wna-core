{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Scientific.Base where

open import Data.Bool.Base                                 using (Bool)
open import Data.Float.Base                                using (Float)
open import Data.Integer.Base                              using (ℤ)
open import Data.Sum.Base                                  using (_⊎_)
open import Foreign.Haskell.Coerce                         using (coerce)
open import Foreign.Haskell.Either as Either               using (Either)
open import Wna.Foreign.Haskell.Base.Data.Int.Base as Int  using (Int)
open import Wna.Data.Scientific.Base               as Safe using ()
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Scientific #-}

postulate
    Scientific : Type
    
    -- Construction
    scientific     : ℤ → Int → Scientific
    
    -- Projections
    coefficient    : Scientific → ℤ
    base10Exponent : Scientific → Int

    -- Predicates
    isFloating     : Scientific → Bool
    isInteger      : Scientific → Bool

    -- todo: Conversions - rational

    -- Conversions - floating & integer
    floatingOrInteger : Scientific → Either Float ℤ
    toFloat           : Scientific → Float
    fromFloat         : Float → Scientific

    -- Normalization
    normalize : Scientific → Scientific
    
floatOrInteger′ : Scientific → Float ⊎ ℤ
floatOrInteger′ x = coerce (floatingOrInteger x)

fromForeign : Scientific → Safe.Scientific
fromForeign x = Safe.mkScientific (coefficient x) (Int.toℤ (base10Exponent x))

toForeign : Safe.Scientific → Scientific
toForeign x = scientific (Safe.coefficient x) (Int.fromℤ (Safe.exponent₁₀ x))

{-# COMPILE GHC Scientific = type Data.Scientific.Scientific #-}

{-# COMPILE GHC scientific        = Data.Scientific.scientific #-}
{-# COMPILE GHC coefficient       = Data.Scientific.coefficient #-}
{-# COMPILE GHC base10Exponent    = Data.Scientific.base10Exponent #-}
{-# COMPILE GHC isFloating        = Data.Scientific.isFloating #-}
{-# COMPILE GHC isInteger         = Data.Scientific.isInteger #-}
{-# COMPILE GHC floatingOrInteger = Data.Scientific.floatingOrInteger #-}
{-# COMPILE GHC toFloat           = Data.Scientific.toRealFloat #-}
{-# COMPILE GHC fromFloat         = Data.Scientific.fromFloatDigits #-}
{-# COMPILE GHC normalize         = Data.Scientific.normalize #-}
