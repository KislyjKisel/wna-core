{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Control.Monad where

open import Wna.Primitive

{-# FOREIGN GHC import qualified Control.Monad #-}

infixl 1 _>>=_ _>>_

postulate
    Monad : ∀{ℓ} → (Type ℓ → Type ℓ) → Type ℓ

    return : ∀{ℓ} {A  } {F : Type ℓ → Type ℓ} ⦃ _ : Monad F ⦄ → A → F A
    _>>=_  : ∀{ℓ} {A B} {F : Type ℓ → Type ℓ} ⦃ _ : Monad F ⦄ → F A → (A → F B) → F B
    _>>_   : ∀{ℓ} {A B} {F : Type ℓ → Type ℓ} ⦃ _ : Monad F ⦄ → F A → F B → F B

{-# FOREIGN GHC data AgdaMonadDict a b = Monad b => AgdaMonadDict #-}
{-# COMPILE GHC Monad = type AgdaMonadDict #-}

{-# COMPILE GHC return = \ ℓ a   f AgdaMonadDict -> Control.Monad.return #-}
{-# COMPILE GHC _>>=_  = \ ℓ a b f AgdaMonadDict -> (Control.Monad.>>=)  #-}
{-# COMPILE GHC _>>_   = \ ℓ a b f AgdaMonadDict -> (Control.Monad.>>)   #-}
