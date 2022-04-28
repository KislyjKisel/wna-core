{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Bundles where

open import Wna.Class.RawMonad.LevelPolymorphic using (RawMonad′; module MkRawMonad′)
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
