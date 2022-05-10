{-# OPTIONS --without-K --safe --guardedness #-}

module Wna.Monad.Free.Guarded.Base where

open import Codata.Guarded.M         using ()           renaming (M to ν)
open import Data.Container.Core      using (Container)
open import Function.Base            using (_$_)
open import Wna.Monad.Free.Container using (FreeC)
open import Wna.Primitive

record FreeT {ℓ} (F M : Container ℓ ℓ) (A : Type ℓ) : Type ℓ where
    constructor mkFree
    field
        runFree : ν $ FreeC F M A

