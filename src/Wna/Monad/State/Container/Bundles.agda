{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Container.Bundles where

open import Data.Container.Core                 using (Container; ⟦_⟧)
open import Wna.Class.RawApplicative            using (RawApplicative)
open import Wna.Class.RawFunctor                using (RawFunctor)
open import Wna.Class.RawMonad                  using (RawMonad; module MkRawMonad)
open import Wna.Monad.Identity.Container as Idc using ()
open import Wna.Monad.State.Container.Base
open import Wna.Primitive

module _ {ℓ} {S : Type ℓ} {M : Container ℓ ℓ} ⦃ M-monad : RawMonad {ℓ} ⟦ M ⟧ ⦄ where
    private
        module M = RawMonad M-monad

    rawMonadT : RawMonad {ℓ} ⟦ StateT S M ⟧
    rawMonadT = MkRawMonad.from:pure,>>= pureT _>>=T_

module _ {ℓ} {S : Type ℓ} where

    rawMonad : RawMonad {ℓ} ⟦ State S ⟧
    rawMonad = rawMonadT ⦃ Idc.rawMonad ⦄

    rawFunctor : RawFunctor {ℓ} ⟦ State S ⟧
    rawFunctor = RawMonad.rawFunctor rawMonad

    rawApplicative : RawApplicative {ℓ} ⟦ State S ⟧
    rawApplicative = RawMonad.rawApplicative rawMonad
