{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Interface where

import Wna.Class.Monad.Ask as Ask
import Wna.Class.Monad.Local as Local
open import Wna.Monad.Identity.Properties renaming (rawMonad to id-rawMonad)
open import Wna.Monad.Reader.Base using (Reader)
open import Wna.Monad.Reader.Instances using (Reader<:Ask; Reader<:Local)
open import Wna.Monad.Reader.Properties using (rawMonad)

module _ {rℓ} {R : Type rℓ} where

    ask : Reader R R
    ask = Ask.ask ⦃ rawMonad ⦄ ⦃ Reader<:Ask ⦃ id-rawMonad ⦄ ⦄

    local : (R → R) → ∀{A} → Reader R A → Reader R A
    local = Local.local ⦃ rawMonad ⦄ ⦃ Reader<:Local ⦃ id-rawMonad ⦄ ⦄
