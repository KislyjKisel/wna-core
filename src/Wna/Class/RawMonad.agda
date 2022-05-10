{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawMonad where

open import Data.Unit                   using (⊤)
open import Function.Base               using (id; _∘′_)
open import Wna.Class.RawApplicative    using (IFun; Fun⇒IFun; RawIApplicative; module IApplicativeFT; module MkRawIApplicative)
open import Wna.Class.RawFunctor        using (Fun)
open import Wna.Primitive

module IMonadFT {iℓ aℓ} {I : Type iℓ} (F : IFun I aℓ) where
    open IApplicativeFT F public

    return : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    return = pure

    _>>=_ : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    _>>=_ = ∀ {A B : Type aℓ} {i j k} → F i j A → (A → F j k B) → F i k B

    join : Type (iℓ ℓ⊔ ℓ↑ aℓ)
    join = ∀ {A : Type aℓ} {i j k} → F i j (F j k A) → F i k A


module MonadFT {aℓ} (F : Fun aℓ) where
    open IMonadFT {aℓ = aℓ} (Fun⇒IFun F) public


mutual
    RawMonad : ∀{aℓ} → Fun aℓ → Type (ℓ↑ aℓ)
    RawMonad F = RawIMonad (Fun⇒IFun F)

    record RawIMonad {iℓ aℓ} {I : Type iℓ} (F : IFun I aℓ) : Type (iℓ ℓ⊔ ℓ↑ aℓ) where
        private module FT = IMonadFT F
        infixl 1 _>>=_ _>>_ _>=>_
        infixr 1 _=<<_ _<=<_

        field
            _>>=_ : FT._>>=_
            join  : FT.join
            
            overlap ⦃ rawIApplicative ⦄ : RawIApplicative F

        open RawIApplicative rawIApplicative public

        rawMonad : ∀{i} → RawMonad (F i i)
        rawMonad = record
            { rawIApplicative = rawApplicative
            ; _>>=_           = _>>=_
            ; join            = join
            }

        return : FT.return
        return = pure

        _>>_ : ∀ {A B : Type aℓ} {i j k} → F i j A → F j k B → F i k B
        _>>_ = _*>_

        _=<<_ : ∀ {A B : Type aℓ} {i j k} → (A → F j k B) → F i j A → F i k B
        f =<< c = c >>= f

        _>=>_ : ∀ {A B C : Type aℓ} {i j k} → (A → F i j B) → (B → F j k C) → (A → F i k C)
        f >=> g = _=<<_ g ∘′ f

        _<=<_ : ∀ {A B C : Type aℓ} {i j k} → (B → F j k C) → (A → F i j B) → (A → F i k C)
        g <=< f = f >=> g


module RawMonad {aℓ} {F : Fun aℓ} (raw : RawMonad F) where
    open RawIMonad raw public
        hiding (rawMonad)


module MkRawIMonad {iℓ aℓ} {I : Type iℓ} {F : IFun I aℓ} where
    private module FT = IMonadFT F

    pure,>>=⇒<*> : FT.pure → FT._>>=_ → FT._<*>_
    pure,>>=⇒<*> pure _>>=_ = λ f x → f >>= λ f′ → x >>= λ x′ → pure (f′ x′)

    pure,>>=⇒rawIApplicative : FT.pure → FT._>>=_ → RawIApplicative F
    pure,>>=⇒rawIApplicative pure _>>=_ = MkRawIApplicative.from:pure,<*> pure (pure,>>=⇒<*> pure _>>=_)

    >>=⇒join : FT._>>=_ → FT.join
    >>=⇒join _>>=_ = λ ffx → ffx >>= id

    fmap,join⇒>>= : FT.map → FT.join → FT._>>=_
    fmap,join⇒>>= map join x f = join (map f x)

    from:pure,>>= : FT.pure → FT._>>=_ → RawIMonad F
    from:pure,>>= pure _>>=_ = record
        { rawIApplicative = pure,>>=⇒rawIApplicative pure _>>=_
        ; _>>=_           = _>>=_
        ; join            = >>=⇒join _>>=_
        }


module MkRawMonad {aℓ} {F : Fun aℓ} where
    open MkRawIMonad {aℓ = aℓ} {F = Fun⇒IFun F} public
        renaming (pure,>>=⇒rawIApplicative to pure,>>=⇒rawApplicative)
