{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Except.Instances where

open import Wna.Monad.Except.Bundles

instance
    _ = rawFunctor
    _ = rawApplicative
    _ = rawMonad
    _ = raise
    _ = handle
    _ = trans
