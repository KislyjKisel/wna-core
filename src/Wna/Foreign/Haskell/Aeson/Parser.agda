{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.Parser where

open import Data.Maybe.Base using (Maybe)
open import Foreign.Haskell.Either using (Either)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson.Types #-}

postulate
    Parser : ∀{ℓ} → Type ℓ → Type ℓ

    parseMaybe  : ∀{ℓ} {A B : Type ℓ} → (A → Parser B) → A → Maybe B
    parseEither : ∀{ℓ} {A B : Type ℓ} → (A → Parser B) → A → Either (List Char) B

{-# FOREIGN GHC type AgdaParser ℓ = Data.Aeson.Types.Parser #-}
{-# COMPILE GHC Parser = type AgdaParser #-}

{-# COMPILE GHC parseMaybe  = \ ℓ a b -> Data.Aeson.Types.parseMaybe #-}
{-# COMPILE GHC parseEither = \ ℓ a b -> Data.Aeson.Types.parseEither #-}
