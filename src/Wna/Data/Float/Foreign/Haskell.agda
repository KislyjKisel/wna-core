{-# OPTIONS --without-K #-}

module Wna.Data.Float.Foreign.Haskell where

open import Wna.Data.Float.Base using (Float)
open import Wna.Primitive

open import Wna.Serialization.Json as Json using ()
open import Wna.Foreign.Haskell.Aeson.Value as Value using ()
open import Wna.Foreign.Haskell.Aeson.ToJson as ToJson using (ToJson)
open import Wna.Foreign.Haskell.Aeson.FromJson as FromJson using (FromJson)
open import Wna.Foreign.Haskell.Aeson.Parser as Parser using ()
open import Foreign.Haskell.Coerce using (coerce)
open import Wna.Monad.Except.Base as Except using ()
open import Data.Sum.Base as ⊎ using ()
open import Data.String.Base as String using ()
open import Function.Base using (_∘′_)

{-# FOREIGN GHC import qualified Data.Aeson #-}
{-# FOREIGN GHC import MAlonzo.Code.Wna.Foreign.Haskell.Aeson.ToJson (AgdaToJsonDict(AgdaToJsonDict)) #-}
{-# FOREIGN GHC import MAlonzo.Code.Wna.Foreign.Haskell.Aeson.FromJson (AgdaFromJsonDict(AgdaFromJsonDict)) #-}

postulate
    toJson   : ToJson Float
    fromJson : FromJson Float

{-# COMPILE GHC toJson   = AgdaToJsonDict   #-}
{-# COMPILE GHC fromJson = AgdaFromJsonDict #-}

json-encode : Json.Encode Float
json-encode = record
    { encode = Value.fromForeign ∘′ ToJson.toJson ⦃ toJson ⦄
    }

json-decode : Json.Decode Float
json-decode = record
    { decode =
        Except.make ∘′
        ⊎.map₁ (liftℓ ∘′ String.fromList) ∘′
        coerce ∘′
        Parser.parseEither (FromJson.parseJson ⦃ fromJson ⦄ ∘′ Value.toForeign)
    }
