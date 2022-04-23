{-# OPTIONS --without-K --safe #-}

module Wna.Monad.Reader.Instances where

open import Wna.Monad.Reader.Bundles

instance
    _ = rawFunctor
    _ = rawApplicative
    _ = rawMonad
    _ = ask
    _ = local
    _ = trans
