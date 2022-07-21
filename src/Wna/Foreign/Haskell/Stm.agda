{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Stm where

open import Data.Bool.Base using (Bool)
open import Data.Unit      using (⊤)
open import IO.Primitive   using (IO)
open import Wna.Foreign.Haskell.Base.Control.Applicative using (Applicative)
open import Wna.Foreign.Haskell.Base.Control.Monad       using (Monad)
open import Wna.Foreign.Haskell.Base.Data.Functor        using (Functor)
open import Wna.Primitive

{-# FOREIGN GHC {-# LANGUAGE LiberalTypeSynonyms #-} #-}
{-# FOREIGN GHC import qualified Control.Concurrent.STM #-}

postulate
    STM : ∀{ℓ} → Type ℓ → Type ℓ

    atomically : ∀{aℓ} {A : Type aℓ} → STM A → IO A
    retry : ∀{aℓ} {A : Type aℓ} → STM A
    orElse : ∀{aℓ} {A : Type aℓ} → STM A → STM A → STM A
    check : Bool → STM ⊤
    -- throwSTM requires Exceptions
    -- catchSTM same

    -- note: `STM` in `Functor STM` is used as a partially applied type synonym which is illegal in haskell
    -- Level argument probably doesn't matter and can be avoided, but even without it generated declaration will probably be expanded like `type T_X_n a = X a` instead of `type T_X_n = X`
    -- linked: https://github.com/agda/agda/issues/753
    -- functor     : ∀{ℓ} → Functor {ℓ} STM
    -- applicative : ∀{ℓ} → Applicative {ℓ} STM
    -- monad       : ∀{ℓ} → Monad {ℓ} STM
    --
    -- Wna.Foreign.Haskell.Stm.monad
    -- d_monad_42 ::
    --   forall xℓ.
    --     MAlonzo.Code.Agda.Primitive.T_Level_14 ->
    --     MAlonzo.Code.Wna.Foreign.Haskell.Base.Control.Monad.T_Monad_14
    --       xℓ (T_STM_10 xℓ)
    -- d_monad_42 = \ ℓ -> AgdaMonadDict

{-# FOREIGN GHC type AgdaSTM ℓ = Control.Concurrent.STM.STM #-}
{-# COMPILE GHC STM = type AgdaSTM #-}

{-# COMPILE GHC atomically = \ aℓ a -> Control.Concurrent.STM.atomically #-}
{-# COMPILE GHC retry      = \ aℓ a -> Control.Concurrent.STM.retry      #-}
{-# COMPILE GHC orElse     = \ aℓ a -> Control.Concurrent.STM.orElse     #-}
{-# COMPILE GHC check      =           Control.Concurrent.STM.check      #-}

-- {-# COMPILE GHC functor     = \ ℓ -> AgdaFunctorDict     #-}
-- {-# COMPILE GHC applicative = \ ℓ -> AgdaApplicativeDict #-}
-- {-# COMPILE GHC monad       = \ ℓ -> AgdaMonadDict       #-}
