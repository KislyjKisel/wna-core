{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Base where

open import Level using (Level; _⊔_)
open import Wna.Class.Monad.Trans using (MonT)
open import Wna.Class.RawApplicative using (IFun; Fun⇒IFun)
open import Wna.Class.RawFunctor using (Fun)
open import Wna.Monad.Identity using (Identity)

record ReaderIT {rℓ} (R : Type rℓ) {iℓ} {I : Type iℓ} (M : IFun I rℓ) (i j : I) (A : Type rℓ) : Type rℓ where
    inductive
    no-eta-equality
    pattern
    constructor mkReader
    field
        runReader : R → M i j A

open ReaderIT public

ReaderT : ∀{rℓ} (R : Type rℓ) → MonT rℓ rℓ
ReaderT R M = ReaderIT R (Fun⇒IFun M) _ _

Reader : ∀{rℓ} (R : Type rℓ) → Fun rℓ  
Reader R = ReaderT R Identity
