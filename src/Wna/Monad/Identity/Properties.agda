{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Properties where

open import Function                                using (flip; id; _$_)
open import Relation.Binary.PropositionalEquality   using (refl)
open import Wna.Class.RawMonad.LevelPolymorphic     using (RawMonad′; module MkRawMonad′)
open import Wna.Monad.Identity.Base
open import Wna.Monad.Trans

rawMonad′ : RawMonad′ Identity
rawMonad′ = MkRawMonad′.from:pure′,>>=′ pure′ _>>=′_

open RawMonad′ rawMonad′ public
    using
    ( rawMonad
    ; rawApplicative; rawApplicative′
    ; rawFunctor; rawFunctor′
    )

rawMonadT′ : RawMonadT′ IdentityT
rawMonadT′ ⦃ M ⦄ = M

rawMonadIT′ : RawMonadIT′ IdentityIT
rawMonadIT′ ⦃ M ⦄ = M
