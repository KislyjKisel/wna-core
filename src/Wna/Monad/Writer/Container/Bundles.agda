{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Writer.Container.Bundles where

open import Wna.Monad.Writer.Container.Base
open import Data.Container.Core                    using (Container; ⟦_⟧)
open import Wna.Class.RawApplicative               using (RawApplicative)
open import Wna.Class.RawFunctor                   using (RawFunctor)
open import Wna.Class.RawMonad                     using (RawMonad; module MkRawMonad)
open import Wna.Class.RawMonoid                    using (RawMonoid)
open import Wna.Monad.Identity.Container    as Idc using ()
open import Wna.Primitive

module _ {ℓ} {W : Type ℓ} ⦃ W-monoid : RawMonoid W ⦄
         {M : Container ℓ ℓ} ⦃ M-monad : RawMonad {ℓ} ⟦ M ⟧ ⦄
         where

    rawMonadT : RawMonad {ℓ} ⟦ WriterT W M ⟧
    rawMonadT = MkRawMonad.from:pure,>>= pureT _>>=T_

    rawFunctorT : RawFunctor {ℓ} ⟦ WriterT W M ⟧
    rawFunctorT = RawMonad.rawFunctor rawMonadT

    rawApplicativeT : RawApplicative {ℓ} ⟦ WriterT W M ⟧
    rawApplicativeT = RawMonad.rawApplicative rawMonadT

module _ {ℓ} {W : Type ℓ} ⦃ W-monoid : RawMonoid W ⦄ where

    rawMonad : RawMonad ⟦ Writer W ⟧
    rawMonad = rawMonadT ⦃ M-monad = Idc.rawMonad ⦄

    rawFunctor : RawFunctor ⟦ Writer W ⟧
    rawFunctor = rawFunctorT ⦃ M-monad = Idc.rawMonad ⦄

    rawApplicative : RawApplicative ⟦ Writer W ⟧
    rawApplicative = rawApplicativeT ⦃ M-monad = Idc.rawMonad ⦄
