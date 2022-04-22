{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Interface where

import Wna.Class.Monad.State as St
open import Data.Unit using (⊤)
open import Wna.Monad.State.Base
open import Wna.Monad.State.Properties
open import Wna.Monad.State.Instances using (StateTI<:IState)
open import Level using (Lift)
open import Wna.Monad.Identity.Properties using () renaming (rawMonad to id-rawMonad)

module _ {sℓ} {S : Type sℓ} where
    
    put : S → State S (Lift sℓ ⊤)
    put = St.iput ⦃ rawMonadTI ⦃ id-rawMonad ⦄ ⦄ ⦃ StateTI<:IState ⦃ id-rawMonad ⦄ ⦄

    get : State S S
    get = St.iget ⦃ rawMonadTI ⦃ id-rawMonad ⦄ ⦄ ⦃ StateTI<:IState ⦃ id-rawMonad ⦄ ⦄
