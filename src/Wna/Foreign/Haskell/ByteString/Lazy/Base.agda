{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.ByteString.Lazy.Base where

open import Data.String.Base using (String)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.ByteString.Lazy #-}
{-# FOREIGN GHC import qualified Data.Text.Encoding #-}

postulate
    ByteString : Type

    decodeUtf8 : ByteString → String
    encodeUtf8 : String     → ByteString

{-# COMPILE GHC ByteString = type Data.ByteString.Lazy.ByteString #-}
{-# COMPILE GHC decodeUtf8 = Data.Text.Encoding.decodeUtf8 #-}
{-# COMPILE GHC encodeUtf8 = Data.Text.Encoding.encodeUtf8 #-}
