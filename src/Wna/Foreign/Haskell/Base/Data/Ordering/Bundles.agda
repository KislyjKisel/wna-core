{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Ordering.Bundles where

open import Wna.Class.Cast using (Cast[_⇒_])
open import Wna.Foreign.Haskell.Base.Data.Ordering.Base using (Ordering; fromForeign; toForeign)

cast-fromForeign : Cast[ Ordering ⇒ _ ]
cast-fromForeign = record { cast = fromForeign }

cast-toForeign : Cast[ _ ⇒ Ordering ]
cast-toForeign = record { cast = toForeign }
