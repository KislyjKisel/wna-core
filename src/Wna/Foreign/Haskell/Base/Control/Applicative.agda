{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Control.Applicative where

open import Data.List.Base using (List)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Applicative #-}

infixl 3 _<|>_
infixl 4 _<*>_ _<*_ _*>_

postulate
    Applicative : ∀{ℓ} → (Type ℓ → Type ℓ) → Type ℓ
    Alternative : ∀{ℓ} → (Type ℓ → Type ℓ) → Type ℓ

    pure   : ∀{ℓ} {A    } {F : Type ℓ → Type ℓ} ⦃ _ : Applicative F ⦄ → A → F A
    _<*>_  : ∀{ℓ} {A B  } {F : Type ℓ → Type ℓ} ⦃ _ : Applicative F ⦄ → F (A → B) → F A → F B
    liftA2 : ∀{ℓ} {A B C} {F : Type ℓ → Type ℓ} ⦃ _ : Applicative F ⦄ → A → B → C → F A → F B → F C
    _<*_   : ∀{ℓ} {A B  } {F : Type ℓ → Type ℓ} ⦃ _ : Applicative F ⦄ → F A → F B → F A
    _*>_   : ∀{ℓ} {A B  } {F : Type ℓ → Type ℓ} ⦃ _ : Applicative F ⦄ → F A → F B → F B

    empty : ∀{ℓ} {A} {F : Type ℓ → Type ℓ} ⦃ _ : Alternative F ⦄ → F A
    _<|>_ : ∀{ℓ} {A} {F : Type ℓ → Type ℓ} ⦃ _ : Alternative F ⦄ → F A → F A → F A
    some  : ∀{ℓ} {A} {F : Type ℓ → Type ℓ} ⦃ _ : Alternative F ⦄ → F A → F (List A)
    many  : ∀{ℓ} {A} {F : Type ℓ → Type ℓ} ⦃ _ : Alternative F ⦄ → F A → F (List A)

{-# FOREIGN GHC data AgdaApplicativeDict a b = Applicative b => AgdaApplicativeDict #-}
{-# COMPILE GHC Applicative = type AgdaApplicativeDict #-}

{-# FOREIGN GHC data AgdaAlternativeDict a b = Alternative b => AgdaAlternativeDict #-}
{-# COMPILE GHC Alternative = type AgdaAlternativeDict #-}

{-# COMPILE GHC pure   = \ ℓ a     f AgdaApplicativeDict -> Control.Applicative.pure   #-}
{-# COMPILE GHC _<*>_  = \ ℓ a b   f AgdaApplicativeDict -> (Control.Applicative.<*>)  #-}
{-# COMPILE GHC liftA2 = \ ℓ a b c f AgdaApplicativeDict -> Control.Applicative.liftA2 #-}
{-# COMPILE GHC _<*_   = \ ℓ a b   f AgdaApplicativeDict -> (Control.Applicative.<*)   #-}
{-# COMPILE GHC _*>_   = \ ℓ a b   f AgdaApplicativeDict -> (Control.Applicative.*>)   #-}

{-# COMPILE GHC empty = \ ℓ a f AgdaAlternativeDict -> Control.Applicative.empty #-}
{-# COMPILE GHC _<|>_ = \ ℓ a f AgdaAlternativeDict -> (Control.Applicative.<|>) #-}
{-# COMPILE GHC some  = \ ℓ a f AgdaAlternativeDict -> Control.Applicative.some  #-}
{-# COMPILE GHC many  = \ ℓ a f AgdaAlternativeDict -> Control.Applicative.many  #-}