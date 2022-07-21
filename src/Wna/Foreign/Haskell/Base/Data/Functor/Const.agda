{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Functor.Const where

open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Functor.Const #-}

postulate
    Const : ∀{ℓ} → Type ℓ → Type ℓ → Type ℓ
    mkConst  : ∀{ℓ} {A B : Type ℓ} → A → Const A B
    getConst : ∀{ℓ} {A B : Type ℓ} → Const A B → A

    -- todo: instances

{-# FOREIGN GHC type AgdaConst l = Data.Functor.Const #-}
{-# COMPILE GHC Const = type AgdaConst #-}
{-# COMPILE GHC mkConst  = \ ℓ a b -> Data.Functor.Const    #-}
{-# COMPILE GHC getConst = \ ℓ a b -> Data.Functor.getConst #-}
