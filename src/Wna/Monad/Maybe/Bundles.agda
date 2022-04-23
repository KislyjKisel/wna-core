{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Maybe.Bundles where

open import Function.Base                               using (id; _∘′_)
open import Wna.Class.Monad.Trans                       using (Trans; Trans′)
open import Wna.Class.RawApplicative.LevelPolymorphic   using (module MkRawApplicative′)
open import Wna.Class.RawFunctor.LevelPolymorphic       using (Fun′; module MkRawFunctor′)
open import Wna.Class.RawMonad                          using (RawMonad; module MkRawMonad)
open import Wna.Class.RawMonad.LevelPolymorphic         using (RawMonad′; module MkRawMonad′)
open import Wna.Monad.Identity                          using (Identity)
open import Wna.Monad.Identity.Bundles as Id            using ()
open import Wna.Monad.Maybe.Base
open import Wna.Monad.Trans                             using (RawMonadT; RawMonadT′)

rawMonad′ : RawMonad′ Maybe
rawMonad′ = record
        { _>>=′_           = _>>=′_ ⦃ Id.rawMonad′ ⦄
        ; join′            = MkRawMonad′.>>=′⇒join′ (_>>=′_ ⦃ Id.rawMonad′ ⦄)
        ; rawIApplicative′ = record
            { pure′       = just
            ; _<*>′_      = ap
            ; liftA2′     = MkRawApplicative′.<$>′,<*>′⇒liftA2′ map ap
            ; _<*′_       = MkRawApplicative′.<$>′,<*>′⇒<*′ map ap
            ; _*>′_       = MkRawApplicative′.<$>′,<*>′⇒*>′ map ap
            ; rawFunctor′ = record
                { _<$>′_ = map
                ; _<$′_  = MkRawFunctor′.<$>′⇒<$′ map
                }
            }
        }

open RawMonad′ rawMonad′ public using
    ( rawMonad
    ; rawApplicative; rawApplicative′
    ; rawFunctor; rawFunctor′
    )

rawMonadT′ : RawMonadT′ MaybeT′
rawMonadT′ ⦃ M ⦄ = MkRawMonad′.from:pure′,>>=′ pure′ _>>=′_
    where module M = RawMonad′ M

rawMonadT : ∀{ℓ} → RawMonadT (MaybeT {ℓ})
rawMonadT ⦃ M ⦄ = MkRawMonad.from:pure,>>= pure _>>=_
    where module M = RawMonad M

trans′ : Trans′ (MaybeT′)
trans′ = record
    { lift′ = lift′
    }

trans : ∀{ℓ} → Trans (MaybeT {ℓ})
trans = record
    { lift = lift
    }
