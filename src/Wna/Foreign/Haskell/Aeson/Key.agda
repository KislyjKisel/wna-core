{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.Key where

open import Data.Char.Base                     using (Char)
open import Data.List.Base                     using (List)
open import Data.String.Base                   using (String)
open import Wna.Foreign.Haskell.Base.Data.Eq   using (Eq)
open import Wna.Foreign.Haskell.Base.Data.Ord  using (Ord)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson.Key #-}
{-# FOREIGN GHC import MAlonzo.Code.Wna.Foreign.Haskell.Base.Data.Ord (AgdaOrdDict(AgdaOrdDict)) #-}
{-# FOREIGN GHC import MAlonzo.Code.Wna.Foreign.Haskell.Base.Data.Eq (AgdaEqDict(AgdaEqDict)) #-}

postulate
    Key : Type

    fromList   : List Char → Key
    toList     : Key       → List Char
    fromString : String    → Key
    toString   : Key       → String

    eq  : Eq Key
    ord : Ord Key

{-# COMPILE GHC Key = type Data.Aeson.Key.Key #-}

{-# COMPILE GHC fromList   = Data.Aeson.Key.fromString #-}
{-# COMPILE GHC toList     = Data.Aeson.Key.toString   #-}
{-# COMPILE GHC fromString = Data.Aeson.Key.fromText   #-}
{-# COMPILE GHC toString   = Data.Aeson.Key.toText     #-}

{-# COMPILE GHC eq  = AgdaEqDict  #-}
{-# COMPILE GHC ord = AgdaOrdDict #-}
