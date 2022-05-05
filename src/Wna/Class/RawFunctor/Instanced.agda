{-# OPTIONS --without-K --safe #-}

module Wna.Class.RawFunctor.Instanced where

open import Wna.Class.RawFunctor using (RawFunctor)

open RawFunctor ⦃...⦄ public
    using (_<$>_; _<$_)
