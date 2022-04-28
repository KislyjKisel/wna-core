{-# OPTIONS --without-K --safe --overlapping-instances #-}

module WnaT.Prelude.A where

open import Wna.Prelude

import Wna.Monad.Identity.Bundles as Id
import Wna.Monad.State.Bundles as State
import Wna.Monad.Maybe.Bundles as Maybe

instance
    Id-rawMonad             = Id.rawMonad
    State-rawMonadTI        = State.rawMonadTI
    State-rawMonadT         = State.rawMonadT
    State-rawFunctor        = State.rawFunctor
    State-rawApplicative    = State.rawApplicative
    State-rawIApplicative   = State.rawIApplicative
    State-trans             = State.trans
    State-istate            = State.istate
    State-state             = State.state

    -- Maybe-rawMonadT = Maybe.rawMonadT
    Maybe-rawMonad = Maybe.rawMonad
    Maybe-rawApplicative = Maybe.rawApplicative

f : ℕ → StateT ℕ Maybe ℕ
f x = do
    put 5
    pure 4

-- 2 rawMonadT in same ctx                  -> ∞ type check
-- 2 rawApplicative                         -> "failed to solve"
-- 2 rawApplicative + overlapping-instances -> long, finite type check
