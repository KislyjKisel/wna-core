{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.ByteString.Lazy.Base where

open import Wna.Foreign.Haskell.ByteString.Strict.Base as Strict using ()
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.ByteString.Lazy #-}

postulate
    ByteString : Type
    
    toStrict   : ByteString → Strict.ByteString
    fromStrict : Strict.ByteString → ByteString

{-# COMPILE GHC ByteString = type Data.ByteString.Lazy.ByteString #-}
{-# COMPILE GHC toStrict   = Data.ByteString.Lazy.toStrict        #-}
{-# COMPILE GHC fromStrict = Data.ByteString.Lazy.fromStrict      #-}
