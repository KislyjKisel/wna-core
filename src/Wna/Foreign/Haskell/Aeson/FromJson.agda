{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.FromJson where

open import Data.Char.Base                           using (Char)
open import Data.List.Base                           using (List)
open import Data.Maybe.Base                          using (Maybe)
open import Foreign.Haskell.Either                   using (Either)
open import Wna.Foreign.Haskell.ByteString.Lazy.Base using (ByteString)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson #-}

postulate
    FromJson : ∀{ℓ} → Type ℓ → Type ℓ

    decode  : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Maybe A
    decode' : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Maybe A

    eitherDecode  : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Either (List Char) A
    eitherDecode' : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Either (List Char) A

{-# FOREIGN GHC data AgdaFromJsonDict a b = Data.Aeson.FromJSON b => AgdaFromJsonDict #-}
{-# COMPILE GHC FromJson = type AgdaFromJsonDict #-}

{-# COMPILE GHC decode        = \ ℓ a d -> Data.Aeson.decode        #-}
{-# COMPILE GHC decode'       = \ ℓ a d -> Data.Aeson.decode'       #-}
{-# COMPILE GHC eitherDecode  = \ ℓ a d -> Data.Aeson.eitherDecode  #-}
{-# COMPILE GHC eitherDecode' = \ ℓ a d -> Data.Aeson.eitherDecode' #-}
