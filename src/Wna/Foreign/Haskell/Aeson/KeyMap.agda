{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.KeyMap where

open import Wna.Foreign.Haskell.Aeson.Key                using (Key)
open import Wna.Foreign.Haskell.Containers.Map.Lazy.Base using (Map)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson.KeyMap #-}

postulate
    KeyMap : ∀{vℓ} → Type vℓ → Type vℓ

    toMap   : ∀{vℓ} {V : Type vℓ} → KeyMap V  → Map Key V
    fromMap : ∀{vℓ} {V : Type vℓ} → Map Key V → KeyMap V

{-# FOREIGN GHC type AgdaKeyMap vℓ = Data.Aeson.KeyMap.KeyMap #-}
{-# COMPILE GHC KeyMap = type AgdaKeyMap #-}

{-# COMPILE GHC toMap   = \ vℓ V -> Data.Aeson.KeyMap.toMap   #-}
{-# COMPILE GHC fromMap = \ vℓ V -> Data.Aeson.KeyMap.fromMap #-}
