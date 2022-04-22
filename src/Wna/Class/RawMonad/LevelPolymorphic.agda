{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawMonad.LevelPolymorphic where

open import Data.Unit                                   using (⊤)
open import Function                                    using (_∘_; id)
open import Wna.Class.RawApplicative.LevelPolymorphic
open import Wna.Class.RawFunctor.LevelPolymorphic       using (Fun′)
open import Wna.Class.RawMonad                          using (RawMonad; RawIMonad)
open import Wna.Primitive

module IMonadFT′ {iℓ} {I : Type iℓ} (F : IFun′ I) where
    open IApplicativeFT′ F public

    return′ : Typeω
    return′ = pure′

    _>>=′_ : Typeω
    _>>=′_ = ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {i j k} → F i j A → (A → F j k B) → F i k B

    join′ : Typeω
    join′ = ∀ {aℓ} {A : Type aℓ} {i j k} → F i j (F j k A) → F i k A


module MonadFT′ {F : Fun′} where
    open IMonadFT′ (Fun′⇒IFun′ F) public


mutual
    RawMonad′ : Fun′ → Typeω
    RawMonad′ F = RawIMonad′ (Fun′⇒IFun′ F)
    
    record RawIMonad′ {iℓ} {I : Type iℓ} (F : IFun′ I) : Typeω where
        private module FT′ = IMonadFT′ F
        infixl 1 _>>=′_ _>>′_ _>=>′_
        infixr 1 _=<<′_ _<=<′_

        field
            _>>=′_           : FT′._>>=′_
            join′            : FT′.join′
            rawIApplicative′ : RawIApplicative′ F

        open RawIApplicative′ rawIApplicative′ public
            
        rawIMonad : ∀{aℓ} → RawIMonad (F {aℓ})
        rawIMonad = record
            { rawIApplicative = rawIApplicative
            ; _>>=_           = _>>=′_
            ; join            = join′
            }

        rawMonad′ : ∀{i} → RawMonad′ (F i i)
        rawMonad′ = record
            { rawIApplicative′ = rawApplicative′
            ; _>>=′_           = _>>=′_
            ; join′            = join′
            }

        private
            module RIM {aℓ} = RawIMonad (rawIMonad {aℓ})
        
        open RIM public
            using (rawMonad)


        return′ : FT′.return′
        return′ = pure′

        _>>′_ : FT′._*>′_
        _>>′_ = _*>′_

        _=<<′_ : ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {i j k} → (A → F j k B) → F i j A → F i k B
        f =<<′ c = c >>=′ f

        _>=>′_ : ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {cℓ} {C : Type cℓ} {i j k} → (A → F i j B) → (B → F j k C) → (A → F i k C)
        f >=>′ g = _=<<′_ g ∘ f

        _<=<′_ : ∀ {aℓ} {A : Type aℓ} {bℓ} {B : Type bℓ} {cℓ} {C : Type cℓ} {i j k} → (B → F j k C) → (A → F i j B) → (A → F i k C)
        g <=<′ f = f >=>′ g


module RawMonad′ {F : Fun′} (raw : RawMonad′ F) where
    open RawIMonad′ raw public
        hiding (rawMonad′; rawIMonad; rawIApplicative; rawIApplicative′)


module MkRawIMonad′ {iℓ} {I : Type iℓ} {F : IFun′ I} where
    private module FT′ = IMonadFT′ F

    pure′,>>=′⇒<*>′ : FT′.pure′ → FT′._>>=′_ → FT′._<*>′_
    pure′,>>=′⇒<*>′ pure′ _>>=′_ = λ f x → f >>=′ λ f′ → x >>=′ λ x′ → pure′ (f′ x′)

    pure′,>>=′⇒rawIApplicative′ : FT′.pure′ → FT′._>>=′_ → RawIApplicative′ F
    pure′,>>=′⇒rawIApplicative′ pure′ _>>=′_ = MkRawIApplicative′.from:pure′,<*>′ pure′ (pure′,>>=′⇒<*>′ pure′ _>>=′_)

    >>=′⇒join′ : FT′._>>=′_ → FT′.join′
    >>=′⇒join′ _>>=′_ = λ ffx → ffx >>=′ id

    from:pure′,>>=′ : FT′.pure′ → FT′._>>=′_ → RawIMonad′ F
    from:pure′,>>=′ pure′ _>>=′_ = record
        { rawIApplicative′ = pure′,>>=′⇒rawIApplicative′ pure′ _>>=′_
        ; _>>=′_           = _>>=′_
        ; join′            = >>=′⇒join′ _>>=′_
        }


module MkRawMonad′ {F : Fun′} where
    open MkRawIMonad′ {F = Fun′⇒IFun′ F} public
        renaming (pure′,>>=′⇒rawIApplicative′ to pure′,>>=′⇒rawApplicative′)
