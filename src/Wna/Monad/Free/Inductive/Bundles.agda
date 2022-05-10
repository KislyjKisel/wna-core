{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Free.Inductive.Bundles where

open import Data.Container.Core                        using (Container; ⟦_⟧)
open import Wna.Class.Monad.Free                       using (MonadFree)
open import Wna.Class.RawApplicative                   using (RawApplicative; module MkRawApplicative)
open import Wna.Class.RawFunctor                       using (RawFunctor; module MkRawFunctor)
open import Wna.Class.RawMonad                         using (RawMonad; module MkRawMonad)
open import Wna.Monad.Free.Inductive.Base
open import Wna.Monad.Identity.Container.Bundles as Id using ()

module _ {ℓ} {F M : Container ℓ ℓ} ⦃ M-monad : RawMonad {aℓ = ℓ} ⟦ M ⟧ ⦄ where
    
    rawMonadT : RawMonad (FreeT F M)
    rawMonadT = record
        { _>>=_           = _>>=_
        ; join            = join
        ; rawIApplicative = record
            { pure       = pure
            ; _<*>_      = _<*>_
            ; liftA2     = MkRawApplicative.<$>,<*>⇒liftA2 map _<*>_
            ; _<*_       = MkRawApplicative.<$>,<*>⇒<* map _<*>_
            ; _*>_       = MkRawApplicative.<$>,<*>⇒*> map _<*>_
            ; rawFunctor = MkRawFunctor.from:<$> map
            }
        }
        where
        _<*>_ = MkRawMonad.pure,>>=⇒<*> pure _>>=_

    monadFree : MonadFree ⟦ F ⟧ (FreeT F M)
    monadFree = record
        { wrap     = wrap
        ; rawMonad = rawMonadT
        }

module _ {ℓ} {F : Container ℓ ℓ} where

    rawMonad : RawMonad (Free F)
    rawMonad = rawMonadT ⦃ Id.rawMonad ⦄

    rawFunctor : RawFunctor (Free F)
    rawFunctor = RawMonad.rawFunctor rawMonad

    rawApplicative : RawApplicative (Free F)
    rawApplicative = RawMonad.rawApplicative rawMonad
