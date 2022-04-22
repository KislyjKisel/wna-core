{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawApplicative.LevelPolymorphic where

open import Data.Product                            using (_×_; _,_)
open import Data.Unit                               using (⊤)
open import Function.Base                           using (const; constᵣ; flip; id)
open import Wna.Class.RawApplicative                using (RawIApplicative)
open import Wna.Class.RawFunctor.LevelPolymorphic   using (Fun′; RawFunctor′; module FunctorFT′; module MkRawFunctor′)
open import Wna.Primitive

IFun′ : ∀{i} → Type i → Typeω
IFun′ I = ∀{aℓ} → I → I → Type aℓ → Type aℓ

Fun′⇒IFun′ : Fun′ → IFun′ ⊤
Fun′⇒IFun′ F = λ _ _ → F

module IApplicativeFT′ {iℓ} {I : Type iℓ} (F : IFun′ I) where
    _<$>′_ : Typeω
    _<$>′_ = ∀ {i j : I} → (FunctorFT′._<$>′_ (F i j))

    _<$′_ : Typeω
    _<$′_ = ∀ {i j : I} → (FunctorFT′._<$′_ (F i j))

    pure′ : Typeω
    pure′ = ∀ {aℓ} {A : Type aℓ} {i} → A → F i i A
    
    _<*>′_ : Typeω
    _<*>′_ = ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {i j k} → F i j (A → B) → F j k A → F i k B

    liftA2′ : Typeω
    liftA2′ = ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {cℓ} {C : Type cℓ} {i j k} → (A → B → C) → F i j A → F j k B → F i k C

    _<*′_ : Typeω
    _<*′_ = ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {i j k} → F i j A → F j k B → F i k A
    
    _*>′_ : Typeω
    _*>′_ = ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {i j k} → F i j A → F j k B → F i k B


module ApplicativeFT′ {F : Fun′} where
    open IApplicativeFT′ (Fun′⇒IFun′ F) public


mutual
    RawApplicative′ : (F : Fun′) → Typeω
    RawApplicative′ F = RawIApplicative′ (Fun′⇒IFun′ F)

    record RawIApplicative′ {i} {I : Type i} (F : IFun′ I) : Typeω where
        private module FT′ = IApplicativeFT′ F
        infixl 4 _<*>′_ _<*′_ _*>′_
        infix  4 _⊗′_

        field
            pure′       : FT′.pure′
            _<*>′_      : FT′._<*>′_
            liftA2′     : FT′.liftA2′
            _<*′_       : FT′._<*′_
            _*>′_       : FT′._*>′_
            rawFunctor′ : ∀{i j} → RawFunctor′ (F i j)
        
        private
            open module RF {i j} = RawFunctor′ (rawFunctor′ {i} {j}) public

        rawIApplicative : ∀{aℓ} → RawIApplicative (F {aℓ})
        rawIApplicative = record
            { rawFunctor = rawFunctor
            ; pure       = pure′
            ; _<*>_      = _<*>′_
            ; liftA2     = liftA2′
            ; _<*_       = _<*′_
            ; _*>_       = _*>′_
            }

        rawApplicative′ : ∀{i} → RawApplicative′ (F i i)
        rawApplicative′ = record
            { rawFunctor′ = rawFunctor′
            ; pure′       = pure′
            ; _<*>′_      = _<*>′_
            ; liftA2′     = liftA2′
            ; _<*′_       = _<*′_
            ; _*>′_       = _*>′_
            }

        private
            open module RIA {aℓ} = RawIApplicative (rawIApplicative {aℓ = aℓ}) public
                using (rawApplicative)

        _⊗′_ : ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {i j k} → F i j A → F j k B → F i k (A × B)
        x ⊗′ y = pure′ _,_ <*>′ x <*>′ y


module RawApplicative′ {F : Fun′} (raw : RawApplicative′ F) where
    open RawIApplicative′ raw public
        hiding (rawIApplicative; rawApplicative′)


module MkRawIApplicative′ {iℓ} {I : Type iℓ} {F : IFun′ I} where
    private module FT′ = IApplicativeFT′ F

    pure′,<*>′⇒rawFunctor′ : FT′.pure′ → FT′._<*>′_ → ∀{i j} → RawFunctor′ (F i j)
    pure′,<*>′⇒rawFunctor′ pure′ _<*>′_ = MkRawFunctor′.from:<$>′ λ g x → pure′ g <*>′ x

    <$>′,<*>′⇒liftA2′ : FT′._<$>′_ → FT′._<*>′_ → FT′.liftA2′
    <$>′,<*>′⇒liftA2′ _<$>′_ _<*>′_ = λ f x y → (f <$>′ x) <*>′ y

    <$>′,<*>′⇒<*′ : FT′._<$>′_ → FT′._<*>′_ → FT′._<*′_
    <$>′,<*>′⇒<*′ _<$>′_ _<*>′_ = λ x y → (const <$>′ x) <*>′ y

    <$>′,<*>′⇒*>′ : FT′._<$>′_ → FT′._<*>′_ → FT′._*>′_
    <$>′,<*>′⇒*>′ _<$>′_ _<*>′_ = λ x y → (constᵣ <$>′ x) <*>′ y

    from:pure′,<*>′ : FT′.pure′ → FT′._<*>′_ → RawIApplicative′ F 
    from:pure′,<*>′ pure′ _<*>′_ = record
        { rawFunctor′ = rawFunctor′
        ; pure′       = pure′
        ; _<*>′_      = _<*>′_
        ; liftA2′     = <$>′,<*>′⇒liftA2′ _<$>′_ _<*>′_
        ; _<*′_       = <$>′,<*>′⇒<*′ _<$>′_ _<*>′_
        ; _*>′_       = <$>′,<*>′⇒*>′ _<$>′_ _<*>′_
        }
        where
        rawFunctor′ : ∀ {i j} → RawFunctor′ (F i j)
        rawFunctor′ = pure′,<*>′⇒rawFunctor′ pure′ _<*>′_
        open module RF {i j} = RawFunctor′ (rawFunctor′ {i = i} {j = j}) using (_<$>′_)

    liftA2′⇒<*>′ : FT′.liftA2′ → FT′._<*>′_
    liftA2′⇒<*>′ liftA2′ = liftA2′ id


module MkRawApplicative′ {F : Fun′} where
    open MkRawIApplicative′ {F = Fun′⇒IFun′ F} public
