{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Aeson.Value where

open import Data.Bool.Base                                             using (Bool)
open import Data.List.Base                                   as List   using ()
open import Data.Product                                     as Σ      using ()
open import Data.String.Base                                           using (String)
open import Data.Tree.AVL.Map                                as AVL    using ()
open import Function.Base                                              using (_$_)
open import Wna.Foreign.Haskell.Aeson.FromJson                         using (FromJson)
open import Wna.Foreign.Haskell.Aeson.Key                    as Key    using ()
open import Wna.Foreign.Haskell.Aeson.KeyMap                 as KeyMap using (KeyMap)
open import Wna.Foreign.Haskell.Aeson.ToJson                           using (ToJson)
open import Wna.Foreign.Haskell.Containers.Map.Lazy.Base     as Map    using ()
open import Wna.Foreign.Haskell.Containers.Vector.Boxed.Base as Vec    using (Vector)
open import Wna.Foreign.Haskell.Scientific.Base              as Sci    using (Scientific)
open import Wna.Serialization.Json.Value                     as Safe   using ()
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

{-# TERMINATING #-}
toForeign : Safe.Value → Value
toForeign (Safe.object x) = object $ KeyMap.fromMap $ Map.toForeignKV ⦃ Key.ord ⦄ (Σ.map Key.fromString toForeign) x
toForeign (Safe.array  x) = array $ Vec.fromList $ List.map toForeign x -- ! termination check failed, but why?
toForeign (Safe.string x) = string x
toForeign (Safe.number x) = number $ Sci.toForeignᵘ x
toForeign (Safe.bool   x) = bool x
toForeign  Safe.null      = null

{-# TERMINATING #-}
fromForeign : Value → Safe.Value
fromForeign (object x) = Safe.object $ Map.fromForeignKV ⦃ Key.ord ⦄ (Σ.map Key.toString fromForeign) $ KeyMap.toMap x
fromForeign (array  x) = Safe.array $ List.map fromForeign $ Vec.toList x -- ! termination check failed (List.map)
fromForeign (string x) = Safe.string x
fromForeign (number x) = Safe.number $ Sci.fromForeignᵘ x
fromForeign (bool   x) = Safe.bool x
fromForeign  null      = Safe.null

postulate
    fromJson : FromJson Value
    toJson   : ToJson   Value

{-# COMPILE GHC Value = data Data.Aeson.Value (Object | Array | String | Number | Bool | Null) #-}
{-# COMPILE GHC fromJson = AgdaFromJsonDict #-}
{-# COMPILE GHC toJson   = AgdaToJsonDict   #-}
