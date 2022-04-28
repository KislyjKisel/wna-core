{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Base where

open import Wna.Class.RawMonad using (module MonadFT)
open import Wna.Primitive

module _ {ℓ} where
    record Identity (A : Type ℓ) : Type ℓ where
        no-eta-equality
        pattern
        constructor mkIdentity
        field
            runIdentity : A

    open Identity public

    pure : MonadFT.pure Identity
    pure x = mkIdentity x

    _>>=_ : MonadFT._>>=_ Identity
    _>>=_ (mkIdentity x) f = f x
