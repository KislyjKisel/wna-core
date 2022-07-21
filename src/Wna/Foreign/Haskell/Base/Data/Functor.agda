{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Functor where

open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Functor #-}

infixl 4 _<$_

postulate
    Functor : ∀{ℓ} → (Type ℓ → Type ℓ) → Type ℓ
    fmap : ∀{ℓ} {A B} {F : Type ℓ → Type ℓ} ⦃ _ : Functor F ⦄ → (A → B) → F A → F B
    _<$_ : ∀{ℓ} {A B} {F : Type ℓ → Type ℓ} ⦃ _ : Functor F ⦄ → A → F B → F A

{-# FOREIGN GHC data AgdaFunctorDict a b = Data.Functor.Functor b => AgdaFunctorDict #-}
{-# COMPILE GHC Functor = type AgdaFunctorDict #-}

{-# COMPILE GHC fmap = \ ℓ a b f AgdaFunctorDict -> Data.Functor.fmap #-}
{-# COMPILE GHC _<$_ = \ ℓ a b f AgdaFunctorDict -> (Data.Functor.<$) #-}
