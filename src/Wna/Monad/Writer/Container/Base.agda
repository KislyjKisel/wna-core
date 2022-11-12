{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Writer.Container.Base where

open import Data.Container.Combinator     as Cc using ()
open import Data.Container.Core                 using (Container; ⟦_⟧)
open import Data.Product                  as Σ  using (_×_; _,_)
open import Data.Unit.Polymorphic               using (⊤)
open import Function.Base                       using (_$′_; _∘′_)
open import Wna.Class.RawMonad                  using (RawMonad)
open import Wna.Class.RawMonoid                 using (RawMonoid)
open import Wna.Data.Container.Conversion as Cc using ()
open import Wna.Monad.Identity.Container as Idc using ()
open import Wna.Primitive

WriterT : ∀{ℓ} (W : Type ℓ) (M : Container ℓ ℓ) → Container ℓ ℓ
WriterT {ℓ} W M = M Cc.∘ (Cc.id {ℓ} {ℓ} Cc.× Cc.const {p = ℓ} W)

Writer : ∀{ℓ} (W : Type ℓ) → Container ℓ ℓ
Writer W = WriterT W Cc.id

module _ {ℓ} {W : Type ℓ} ⦃ W-monoid : RawMonoid W ⦄
         {M : Container ℓ ℓ} ⦃ M-monad : RawMonad {ℓ} ⟦ M ⟧ ⦄
         where

    private
        module W = RawMonoid W-monoid
        module M = RawMonad M-monad

        F : Type ℓ → Type ℓ
        F = ⟦ WriterT W M ⟧

    makeT : ∀{A} → ⟦ M ⟧ (A × W) → F A
    makeT = Cc.composition-to ∘′ M.map (Cc.product-to ∘′ Σ.map Cc.id-to Cc.const-to)

    runT : ∀{A} → F A → ⟦ M ⟧ (A × W)
    runT = M.map (Σ.map Cc.id-from Cc.const-from ∘′ Cc.product-from) ∘′ Cc.composition-from

    pureT : ∀{A} → A → F A
    pureT = makeT ∘′ M.pure ∘′ (_, W.mempty)

    _>>=T_ : ∀{A B} → F A → (A → F B) → F B
    _>>=T_ x f = Cc.composition-to $′ runT x M.>>= λ (x' , w) →
        M.map
            (Cc.product-map $′ Σ.map₂′ $′ Cc.const-map $′ W.mappend w) $′
            Cc.composition-from $′ f x'

    writerT : ∀{A} → A × W → F A
    writerT = makeT ∘′ M.pure

    tellT : W → F ⊤
    tellT = makeT ∘′ M.pure ∘′ (_ ,_)

    listenT : ∀{A} → F A → F (A × W)
    listenT = Cc.composition-map $′ M.map $′ Cc.product-map $′ λ (idA , cW) →
        let w = Cc.const-from cW
        in Cc.id-map {ℓ} {ℓ} (_, w) idA , Cc.const-to w

    passT : ∀{A} → F (A × (W → W)) → F A
    passT = makeT ∘′ M.map (λ ((x , f) , w) → x , f w) ∘′ runT

module _ {ℓ} {W : Type ℓ} ⦃ W-monoid : RawMonoid W ⦄ where
    private
        F : Type ℓ → Type ℓ
        F = ⟦ Writer W ⟧

    make : ∀{A} → A × W → F A
    make = makeT ⦃ M-monad = Idc.rawMonad ⦄ ∘′ Idc.mkIdentity

    run : ∀{A} → F A → A × W
    run = Idc.runIdentity ∘′ runT ⦃ M-monad = Idc.rawMonad ⦄

    pure : ∀{A} → A → F A
    pure = pureT ⦃ M-monad = Idc.rawMonad ⦄

    _>>=_ : ∀{A B} → F A → (A → F B) → F B
    _>>=_ = _>>=T_ ⦃ M-monad = Idc.rawMonad ⦄

    writer : ∀{A} → A × W → F A
    writer = writerT ⦃ M-monad = Idc.rawMonad ⦄

    tell : W → F ⊤
    tell = tellT ⦃ M-monad = Idc.rawMonad ⦄

    listen : ∀{A} → F A → F (A × W)
    listen = listenT ⦃ M-monad = Idc.rawMonad ⦄

    pass : ∀{A} → F (A × (W → W)) → F A
    pass = passT ⦃ M-monad = Idc.rawMonad ⦄
