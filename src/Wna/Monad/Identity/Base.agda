{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Identity.Base where

open import Function.Base                           using (flip; id; _$_)
open import Wna.Class.RawFunctor.LevelPolymorphic   using (Fun′)
open import Wna.Class.RawMonad.LevelPolymorphic     using (module MonadFT′)
open import Wna.Monad.Trans
open import Wna.Primitive

Identity : Fun′
Identity = id

IdentityT : MonT′
IdentityT M = M

IdentityIT : MonIT′
IdentityIT M = M

pure′ = id

_>>=′_ : MonadFT′._>>=′_
_>>=′_ = flip _$_
