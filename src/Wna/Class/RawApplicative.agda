{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawApplicative where

open import Data.Product                    using (_×_; _,_)
open import Data.Unit                       using (⊤; tt)
open import Data.Unit.Polymorphic as ⊤ℓ*    using ()
open import Function.Base                   using (const; constᵣ; flip; id)
open import Wna.Class.Foldable              using (Foldable)
open import Wna.Class.RawFunctor            using (Fun; RawFunctor; module FunctorFT; module MkRawFunctor)
open import Wna.Primitive

IFun : ∀{iℓ} → Type iℓ → (ℓ : Level) → Type (iℓ ℓ⊔ ℓ↑ ℓ)
IFun I ℓ = I → I → Type ℓ → Type ℓ

Fun⇒IFun : ∀{aℓ} → Fun aℓ → IFun ⊤ aℓ
Fun⇒IFun F = λ _ _ → F

module IApplicativeFT {iℓ aℓ} {I : Type iℓ} (F : IFun I aℓ) where
    _<$>_ : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    _<$>_ = ∀ {i j : I} → (FunctorFT._<$>_ (F i j))

    map = _<$>_

    _<$_ : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    _<$_ = ∀ {i j : I} → (FunctorFT._<$_ (F i j))

    pure : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    pure = ∀ {A : Type aℓ} {i} → A → F i i A
    
    _<*>_ : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    _<*>_ = ∀ {A B : Type aℓ} {i j k} → F i j (A → B) → F j k A → F i k B

    liftA2 : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    liftA2 = ∀ {A B C : Type aℓ} {i j k} → (A → B → C) → F i j A → F j k B → F i k C

    _<*_ : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    _<*_ = ∀ {A B : Type aℓ} {i j k} → F i j A → F j k B → F i k A
    
    _*>_ : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    _*>_ = ∀ {A B : Type aℓ} {i j k} → F i j A → F j k B → F i k B


module ApplicativeFT {aℓ} (F : Fun aℓ) where
    open IApplicativeFT {aℓ = aℓ} (Fun⇒IFun F) public


mutual
    RawApplicative : ∀{aℓ} → Fun aℓ → Type (ℓ↑ aℓ)
    RawApplicative F = RawIApplicative (Fun⇒IFun F)

    record RawIApplicative {iℓ aℓ} {I : Type iℓ} (F : IFun I aℓ) : Type (iℓ ℓ⊔ ℓ↑ aℓ) where
        private module FT = IApplicativeFT F
        infixl 4 _<*>_ _<*_ _*>_
        infix  4 _⊗_

        field
            pure   : FT.pure
            _<*>_  : FT._<*>_
            liftA2 : FT.liftA2
            _<*_   : FT._<*_
            _*>_   : FT._*>_

            overlap ⦃ rawFunctor ⦄ : ∀{i j} → RawFunctor (F i j)

        rawApplicative : ∀{i} → RawApplicative (F i i)
        rawApplicative = record
            { rawFunctor = rawFunctor
            ; pure       = pure
            ; _<*>_        = _<*>_
            ; liftA2     = liftA2
            ; _<*_       = _<*_
            ; _*>_       = _*>_
            }

        private
            module RF {i j} = RawFunctor (rawFunctor {i} {j})

        open RF public

        _⊗_ : ∀ {A B : Type aℓ} {i j k} → F i j A → F j k B → F i k (A × B)
        x ⊗ y = (_,_) <$> x <*> y

        zipWith : ∀ {A B C : Type aℓ} {i j k} → (A → B → C) → F i j A → F j k B → F i k C
        zipWith f x y = f <$> x <*> y

        zip : ∀ {A B : Type aℓ} {i j k} → F i j A → F j k B → F i k (A × B)
        zip = zipWith _,_


module RawApplicative {aℓ} {F : Type aℓ → Type aℓ} (raw : RawApplicative F) where
    open RawIApplicative raw public
        hiding (rawApplicative)

    traverse¡ : ∀{T : Type aℓ → Type aℓ} ⦃ _ : Foldable T ⦄ {A B : Type aℓ} → (A → F B) → T A → F ⊤ℓ*.⊤
    traverse¡ ⦃ Fld ⦄ f = foldr (λ x k → f x *> k) (pure ⊤ℓ*.tt)
        where open Foldable Fld

    for¡ = λ{T} ⦃ Fld ⦄ {A} {B} → flip (traverse¡ {T} ⦃ Fld ⦄ {A} {B})

    sequence¡ : ∀{T : Type aℓ → Type aℓ} ⦃ _ : Foldable T ⦄ {A : Type aℓ} → T (F A) -> F ⊤ℓ*.⊤
    sequence¡ ⦃ Fld ⦄ = foldr (_*>_) (pure ⊤ℓ*.tt)
        where open Foldable Fld

module MkRawIApplicative {iℓ aℓ} {I : Type iℓ} {F : IFun I aℓ} where
    private module FT = IApplicativeFT F

    pure,<*>⇒rawFunctor : FT.pure → FT._<*>_ → ∀{i j} → RawFunctor (F i j)
    pure,<*>⇒rawFunctor pure _<*>_ = MkRawFunctor.from:<$> λ g x → pure g <*> x

    <$>,<*>⇒liftA2 : FT._<$>_ → FT._<*>_ → FT.liftA2
    <$>,<*>⇒liftA2 _<$>_ _<*>_ = λ f x y → (f <$> x) <*> y

    <$>,<*>⇒<* : FT._<$>_ → FT._<*>_ → FT._<*_
    <$>,<*>⇒<* _<$>_ _<*>_ = λ x y → (const <$> x) <*> y

    <$>,<*>⇒*> : FT._<$>_ → FT._<*>_ → FT._*>_
    <$>,<*>⇒*> _<$>_ _<*>_ = λ x y → (constᵣ <$> x) <*> y

    from:pure,<*> : FT.pure → FT._<*>_ → RawIApplicative F 
    from:pure,<*> pure _<*>_ = record
        { rawFunctor = rawFunctor
        ; pure       = pure
        ; _<*>_        = _<*>_
        ; liftA2     = <$>,<*>⇒liftA2 _<$>_ _<*>_
        ; _<*_       = <$>,<*>⇒<* _<$>_ _<*>_
        ; _*>_       = <$>,<*>⇒*> _<$>_ _<*>_
        }
        where
        rawFunctor : ∀ {i j} → RawFunctor (F i j)
        rawFunctor = pure,<*>⇒rawFunctor pure _<*>_
        open module RF {i j} = RawFunctor (rawFunctor {i} {j}) using (_<$>_)

    liftA2⇒<*> : FT.liftA2 → FT._<*>_
    liftA2⇒<*> liftA2 = liftA2 id


module MkRawApplicative {aℓ} {F : Fun aℓ} where
    open MkRawIApplicative {aℓ = aℓ} {F = Fun⇒IFun F} public

module Instanced where
    open RawIApplicative ⦃...⦄ public
        using
        ( pure ; liftA2
        ; _<*>_ ; _<*_ ; _*>_
        )
