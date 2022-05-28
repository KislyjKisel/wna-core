{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.Value.Base where

open import Data.Bool.Base                                             using (Bool)
open import Data.String.Base                                           using (String)
open import Wna.Foreign.Haskell.Aeson.KeyMap                 as KeyMap using (KeyMap)
open import Wna.Foreign.Haskell.Containers.Vector.Boxed.Base as Vec    using (Vector)
open import Wna.Foreign.Haskell.Scientific.Base              as Sci    using (Scientific)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Aeson #-}

{-# NO_POSITIVITY_CHECK #-}
data Value : Type where
    object : KeyMap Value → Value
    array  : Vector Value → Value
    string : String       → Value
    number : Scientific   → Value
    bool   : Bool         → Value
    null   :                Value

{-# COMPILE GHC Value = data Data.Aeson.Value (Data.Aeson.Object | Data.Aeson.Array | Data.Aeson.String | Data.Aeson.Number | Data.Aeson.Bool | Data.Aeson.Null) #-}