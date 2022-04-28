{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Instances where

import Wna.Monad.Identity.Bundles  as Identity
import Wna.Monad.Maybe.Bundles     as Maybe
import Wna.Monad.Except.Bundles    as Except
import Wna.Monad.Reader.Bundles    as Reader
import Wna.Monad.State.Bundles     as State

-- instance
    -- Identity-rawMonad = Identity.rawMonad
    
    -- State-rawMonadTI        = State.rawMonadTI
    -- -- State-rawMonadIT        = State.rawMonadIT
    -- -- State-rawMonadT         = State.rawMonadT
    -- State-rawFunctor        = State.rawFunctor
    -- State-rawApplicative    = State.rawApplicative
    -- State-rawIApplicative   = State.rawIApplicative
    -- State-rawMonad          = State.rawMonad
    -- State-rawIMonad         = State.rawIMonad
    -- State-trans             = State.trans
    -- State-istate            = State.istate
    -- State-state             = State.state
