{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Maybe.Properties where

open import Data.Maybe
open import Function using (_∘′_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Wna.Class.Applicative using (Applicative)
open import Wna.Class.Applicative.Definitions using (IsApplicative)
open import Wna.Class.Applicative.LevelPolymorphic using (Applicative′)
open import Wna.Class.Functor using (Functor)
open import Wna.Class.Functor.Definitions using (IsFunctor)
open import Wna.Class.Functor.LevelPolymorphic using (Functor′)
open import Wna.Class.Monad using (Monad)
open import Wna.Class.Monad.Definitions using (IsMonad)
open import Wna.Class.Monad.LevelPolymorphic using (Monad′)
open import Wna.Class.Monad.Trans
open import Wna.Class.RawApplicative.LevelPolymorphic using (module MkRawApplicative′)
open import Wna.Class.RawFunctor.LevelPolymorphic using (Fun′; module MkRawFunctor′)
open import Wna.Class.RawMonad using (RawIMonad; RawMonad; module MkRawMonad)
open import Wna.Class.RawMonad.LevelPolymorphic
open import Wna.Monad.Identity using (Identity)
open import Wna.Monad.Maybe.Base

monad′ : Monad′ Maybe
monad′ = record
    { rawIMonad′ = record
        { _>>=′_           = _>>=_
        ; join′            = MkRawMonad′.>>=′⇒join′ _>>=_
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
    ; isMonad    = record
        { <*>~pure,>>= = λ{ nothing  x        → refl
                          ; (just f) nothing  → refl
                          ; (just f) (just x) → refl
                          }
        ; >>=-identityˡ = λ x f → refl
        ; >>=-identityʳ = λ{ (just x) → refl
                           ; nothing  → refl
                           }
        ; >>=-assoc = λ{(just x) f g → refl
                      ; nothing  f g → refl
                      }
        ; isApplicative = record
            { liftA2~<$>,<*> = λ f → λ{ (just x) y → refl
                                      ; nothing  y → refl
                                      }
            ; <*>~liftA2 = λ{ (just f) x → refl
                            ; nothing  x → refl
                            }
            ; <*~liftA2 = λ{ (just x) y → refl
                           ; nothing  y → refl
                           }
            ; *>~<$,<*> = λ{ (just x) y → refl
                           ; nothing  y → refl
                           }
            ; <*>-identityˡ = λ{ (just x) → refl
                               ; nothing  → refl
                               }
            ; pure-homo-$ = λ f x → refl
            ; <*>-pure-inter = λ{ (just f) x → refl
                                ; nothing  x → refl
                                }
            ; pure-preserve-∘ = λ{ nothing  g        x        → refl
                                 ; (just f) nothing  x        → refl
                                 ; (just f) (just g) nothing  → refl
                                 ; (just f) (just g) (just x) → refl
                                 }
            ; <$>-pure = λ f x → refl
            ; isFunctor = record
                { <$~<$> = λ x fy → refl
                ; <$>-identityˡ = λ{ (just x) → refl
                                   ; nothing  → refl
                                   }
                ; <$>-preserve-∘ = λ f g → λ{ (just x) → refl
                                            ; nothing  → refl
                                            }
                }
            }
        }
    }

open Monad′ monad′ public using
    ( rawMonad′; rawMonad; monad
    ; applicative; applicative′; rawApplicative; rawApplicative′
    ; functor; functor′; rawFunctor; rawFunctor′
    )

rawMonadT′ : RawMonadT′ MaybeT′
rawMonadT′ ⦃ M ⦄ = MkRawMonad′.from:pure′,>>=′ (M.return′ ∘′ just) λ x f → x M.>>=′ maybe′ f (M.return′ nothing)
    where module M = RawMonad′ M

rawMonadT : ∀{ℓ} → RawMonadT (MaybeT {ℓ})
rawMonadT ⦃ M ⦄ = MkRawMonad.from:pure,>>= (M.return ∘′ just) λ x f → x M.>>= maybe′ f (M.return nothing)
    where module M = RawMonad M
