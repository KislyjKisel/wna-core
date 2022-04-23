{-# OPTIONS --without-K --safe #-}

module Wna.Monad.State.Instances where

open import Wna.Monad.State.Bundles

instance
    _ = rawFunctor
    _ = rawApplicative
    _ = rawIApplicative
    _ = rawMonad
    _ = rawIMonad
    _ = istate
    _ = state
    _ = trans
