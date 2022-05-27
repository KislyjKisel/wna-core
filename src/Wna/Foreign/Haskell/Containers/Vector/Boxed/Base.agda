{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Containers.Vector.Boxed.Base where

open import Data.Bool.Base                         using (Bool)
open import Data.List.Base                         using (List)
open import Data.Maybe.Base                        using (Maybe) 
open import Wna.Foreign.Haskell.Base.Data.Int.Base using (Int)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Vector #-}

postulate
    Vector : ∀{ℓ} → Type ℓ → Type ℓ

    -- Length information
    length : ∀{ℓ} {A : Type ℓ} → Vector A → Int
    null   : ∀{ℓ} {A : Type ℓ} → Vector A → Bool

    -- Indexing
    unsafeLookup  : ∀{ℓ} {A : Type ℓ} → Vector A → Int → A
    lookup        : ∀{ℓ} {A : Type ℓ} → Vector A → Int → Maybe A
    unsafeHead    : ∀{ℓ} {A : Type ℓ} → Vector A → A
    unsafeLast    : ∀{ℓ} {A : Type ℓ} → Vector A → A
    unsafe!Lookup : ∀{ℓ} {A : Type ℓ} → Vector A → Int → A
    unsafe!Head   : ∀{ℓ} {A : Type ℓ} → Vector A → A
    unsafe!Last   : ∀{ℓ} {A : Type ℓ} → Vector A → A 

    -- todo: monadic indexing, slicing

    -- Construction
    empty     : ∀{ℓ} {A : Type ℓ} → Vector A
    singleton : ∀{ℓ} {A : Type ℓ} → A → Vector A
    replicate : ∀{ℓ} {A : Type ℓ} → Int → A → Vector A
    generate  : ∀{ℓ} {A : Type ℓ} → Int → (Int → A) → Vector A
    iterateN  : ∀{ℓ} {A : Type ℓ} → Int → (A → A) → A → Vector A

    -- todo: monadic initialization, unfolding, enumeration, concatenation, "force", modifying, accum etc...

    -- Conversions

    toList          : ∀{ℓ} {A : Type ℓ} →       Vector A → List   A
    fromList        : ∀{ℓ} {A : Type ℓ} →       List   A → Vector A
    unsafeFromListN : ∀{ℓ} {A : Type ℓ} → Int → List   A → Vector A 


{-# FOREIGN GHC type AgdaVectorBoxed ℓ = Data.Vector.Vector #-}
{-# COMPILE GHC Vector = type AgdaVectorBoxed #-}

{-# COMPILE GHC length          = \ ℓ a -> Data.Vector.length      #-}
{-# COMPILE GHC null            = \ ℓ a -> Data.Vector.null        #-}
{-# COMPILE GHC unsafeLookup    = \ ℓ a -> (Data.Vector.!)         #-}
{-# COMPILE GHC lookup          = \ ℓ a -> (Data.Vector.!?)        #-}
{-# COMPILE GHC unsafeHead      = \ ℓ a -> Data.Vector.head        #-}
{-# COMPILE GHC unsafeLast      = \ ℓ a -> Data.Vector.last        #-}
{-# COMPILE GHC unsafe!Lookup   = \ ℓ a -> Data.Vector.unsafeIndex #-}
{-# COMPILE GHC unsafe!Head     = \ ℓ a -> Data.Vector.unsafeHead  #-}
{-# COMPILE GHC unsafe!Last     = \ ℓ a -> Data.Vector.unsafeLast  #-}
{-# COMPILE GHC empty           = \ ℓ a -> Data.Vector.empty       #-}
{-# COMPILE GHC singleton       = \ ℓ a -> Data.Vector.singleton   #-}
{-# COMPILE GHC replicate       = \ ℓ a -> Data.Vector.replicate   #-}
{-# COMPILE GHC generate        = \ ℓ a -> Data.Vector.generate    #-}
{-# COMPILE GHC iterateN        = \ ℓ a -> Data.Vector.iterateN    #-}
{-# COMPILE GHC toList          = \ ℓ a -> Data.Vector.toList      #-}
{-# COMPILE GHC fromList        = \ ℓ a -> Data.Vector.fromList    #-}
{-# COMPILE GHC unsafeFromListN = \ ℓ a -> Data.Vector.fromListN   #-}
