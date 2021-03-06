{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.FromJson where

open import Data.Char.Base                           using (Char)
open import Data.List.Base                           using (List)
open import Data.Maybe.Base                          using (Maybe)
open import Foreign.Haskell.Either                   using (Either)
open import IO.Primitive                             using (IO)
open import Wna.Foreign.Haskell.Aeson.Value.Base     using (Value)
open import Wna.Foreign.Haskell.Aeson.Parser         using (Parser)
open import Wna.Foreign.Haskell.ByteString.Lazy.Base using (ByteString)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson #-}

postulate
    FromJson : ∀{ℓ} → Type ℓ → Type ℓ

    decode  : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Maybe A
    decode' : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Maybe A

    parseJson : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → Value → Parser A 

    eitherDecode  : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Either (List Char) A
    eitherDecode' : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → ByteString → Either (List Char) A

    eitherDecodeFileStrict' : ∀{ℓ} {A : Type ℓ} ⦃ _ : FromJson A ⦄ → List Char → IO (Either (List Char) A)

{-# FOREIGN GHC data AgdaFromJsonDict a b = Data.Aeson.FromJSON b => AgdaFromJsonDict #-}
{-# COMPILE GHC FromJson = type AgdaFromJsonDict #-}

{-# COMPILE GHC decode                  = \ ℓ a AgdaFromJsonDict -> Data.Aeson.decode                  #-}
{-# COMPILE GHC decode'                 = \ ℓ a AgdaFromJsonDict -> Data.Aeson.decode'                 #-}
{-# COMPILE GHC parseJson               = \ ℓ a AgdaFromJsonDict -> Data.Aeson.parseJSON               #-}
{-# COMPILE GHC eitherDecode            = \ ℓ a AgdaFromJsonDict -> Data.Aeson.eitherDecode            #-}
{-# COMPILE GHC eitherDecode'           = \ ℓ a AgdaFromJsonDict -> Data.Aeson.eitherDecode'           #-}
{-# COMPILE GHC eitherDecodeFileStrict' = \ ℓ a AgdaFromJsonDict -> Data.Aeson.eitherDecodeFileStrict' #-}
