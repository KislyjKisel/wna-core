{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Container.Base where

open import Data.Container.Combinator     as Cc  using ()
open import Data.Container.Core                  using (Container; ⟦_⟧)
open import Data.Product                  as Σ   using (proj₁; proj₂; _,_; _×_)
open import Function.Base                        using (case_of_; flip; _$′_; _∘′_)
open import Wna.Class.RawMonad                   using (RawMonad)
open import Wna.Data.Container.Conversion as Ccp using ()
open import Wna.Primitive
open import Wna.Monad.Identity.Container  as Idc using ()
open import Wna.Monad.Identity            as Id  using ()
open import Wna.Monad.State.Base          as St  using ()

-- todo: indexed state monad as a container

module _ {ℓ} where

    StateT : (S : Type ℓ) (M : Container ℓ ℓ) → Container ℓ ℓ
    StateT S M = Cc.const[ S ]⟶ (M Cc.∘ (Cc.id {s = ℓ} {p = ℓ} Cc.× Cc.const {p = ℓ} S))

    State : (S : Type ℓ) → Container ℓ ℓ
    State S = StateT S Idc.Identity

module _ {ℓ} {S : Type ℓ} {M : Container ℓ ℓ} ⦃ M-monad : RawMonad {ℓ} ⟦ M ⟧ ⦄ where
    private
        module M = RawMonad M-monad

    makeT : {A : Type ℓ} → (S → ⟦ M ⟧ (A × S)) → ⟦ StateT S M ⟧ A
    makeT f = Ccp.constexp-to $′
        Ccp.composition-to ∘′
        M.map (Ccp.product-to ∘′ Σ.map Ccp.id-to Ccp.const-to) ∘′
        f

    runT : {A : Type ℓ} → ⟦ StateT S M ⟧ A → S → ⟦ M ⟧ (A × S)
    runT m s = flip M.map
        (Ccp.composition-from $′ Ccp.constexp-from {C = M Cc.∘ (Cc.id Cc.× Cc.const S)} m s)
        (Σ.map Ccp.id-from Ccp.const-from ∘′ Ccp.product-from)

    evalT : ∀{A : Type ℓ} → ⟦ StateT S M ⟧ A → S → ⟦ M ⟧ A
    evalT m = M.map proj₁ ∘′ runT m

    execT : ∀{A : Type ℓ} → ⟦ StateT S M ⟧ A → S → ⟦ M ⟧ S
    execT m = M.map proj₂ ∘′ runT m

    to : ∀{A : Type ℓ} {M'} → (∀{A} → M' A → ⟦ M ⟧ A) → St.StateT S M' A → ⟦ StateT S M ⟧ A
    to m-repr m = makeT (m-repr ∘′ St.runT m)

    from : ∀{A : Type ℓ} {M'} → (∀{A} → ⟦ M ⟧ A → M' A) → ⟦ StateT S M ⟧ A → St.StateT S M' A
    from m-repr m = St.makeT (m-repr ∘′ runT m)

    pureT : ∀{A : Type ℓ} → A → ⟦ StateT S M ⟧ A
    pureT = to (M.pure ∘′ Id.runIdentity) ∘′ St.pure

    _>>=T_ : ∀{A B : Type ℓ} → ⟦ StateT S M ⟧ A → (A → ⟦ StateT S M ⟧ B) → ⟦ StateT S M ⟧ B
    _>>=T_ {A} x f = makeT λ s → runT x s M.>>= λ(x' , s') → runT (f x') s'

module _ {ℓ} {S : Type ℓ} where

    make : {A : Type ℓ} → (S → A × S) → ⟦ State S ⟧ A
    make f = makeT ⦃ Idc.rawMonad ⦄ (Idc.mkIdentity ∘′ f)

    run : {A : Type ℓ} → ⟦ State S ⟧ A → S → A × S
    run m = Idc.runIdentity ∘′ runT ⦃ Idc.rawMonad ⦄ m

    eval : {A : Type ℓ} → ⟦ State S ⟧ A → S → A
    eval m = proj₁ ∘′ run m

    exec : {A : Type ℓ} → ⟦ State S ⟧ A → S → S
    exec m = proj₂ ∘′ run m

    pure : ∀{A : Type ℓ} → A → ⟦ State S ⟧ A
    pure = pureT ⦃ Idc.rawMonad ⦄

    _>>=_ : ∀{A B : Type ℓ} → ⟦ State S ⟧ A → (A → ⟦ State S ⟧ B) → ⟦ State S ⟧ B
    _>>=_ = _>>=T_ ⦃ Idc.rawMonad ⦄
