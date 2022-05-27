{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.ToJson where

open import Wna.Foreign.Haskell.ByteString.Lazy.Base using (ByteString)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson #-}

postulate
    ToJson : ∀{ℓ} → Type ℓ → Type ℓ

    encode  : ∀{ℓ} {A : Type ℓ} ⦃ _ : ToJson A ⦄ → A → ByteString

{-# FOREIGN GHC data AgdaToJsonDict a b = Data.Aeson.ToJSON b => AgdaToJsonDict #-}
{-# COMPILE GHC ToJson = type AgdaToJsonDict #-}

{-# COMPILE GHC encode = \ ℓ a d -> Data.Aeson.encode #-}
