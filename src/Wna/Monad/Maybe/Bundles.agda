{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Maybe.Bundles where

open import Data.Maybe.Base                  renaming (_>>=_ to mb-bind)
open import Function.Base                    using (id; _∘_)
open import Wna.Class.Monad.Trans            using (Trans)
open import Wna.Class.RawApplicative         using (module MkRawApplicative)
open import Wna.Class.RawFunctor             using (Fun; module MkRawFunctor)
open import Wna.Class.RawMonad               using (RawMonad; module MkRawMonad)
open import Wna.Monad.Identity               using (Identity)
open import Wna.Monad.Identity.Bundles as Id using ()
open import Wna.Monad.Maybe.Base
open import Wna.Monad.Trans

module _ {ℓ} where

    rawMonad : RawMonad (Maybe {a = ℓ})
    rawMonad = record
            { _>>=_           = mb-bind
            ; join            = MkRawMonad.>>=⇒join mb-bind
            ; rawIApplicative = record
                { pure       = just
                ; _<*>_      = ap
                ; liftA2     = MkRawApplicative.<$>,<*>⇒liftA2 map ap
                ; _<*_       = MkRawApplicative.<$>,<*>⇒<* map ap
                ; _*>_       = MkRawApplicative.<$>,<*>⇒*> map ap
                ; rawFunctor = record
                    { _<$>_ = map
                    ; _<$_  = MkRawFunctor.<$>⇒<$ map
                    }
                }
            }

    rawMonadT : RawMonadT (MaybeT {ℓ})
    rawMonadT ⦃ M ⦄ = MkRawMonad.from:pure,>>= pure _>>=_

    rawApplicative : RawMonadT-RawApplicative (MaybeT {ℓ})
    rawApplicative = RawMonad.rawApplicative rawMonadT

    rawFunctor : RawMonadT-RawFunctor (MaybeT {ℓ})
    rawFunctor = RawMonad.rawFunctor rawMonadT

    trans : Trans (MaybeT {ℓ = ℓ})
    trans = record
        { lift = lift
        } 
