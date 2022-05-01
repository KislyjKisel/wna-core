{-# OPTIONS --without-K --guardedness --type-in-type #-}

module Wna.Monad.IO.Bundles where

open import Wna.Monad.IO.Base
open import Wna.Class.RawApplicative using (RawApplicative; module MkRawApplicative)
open import Wna.Class.RawFunctor     using (RawFunctor; module MkRawFunctor)
open import Wna.Class.RawMonad       using (RawMonad; module MkRawMonad)

rawFunctor : RawFunctor IO
rawFunctor = record
    { _<$>_ = _<$>_
    ; _<$_  = _<$_
    }

rawApplicative : RawApplicative IO
rawApplicative = record
    { pure       = pure
    ; _<*>_      = _<*>_
    ; liftA2     = MkRawApplicative.<$>,<*>⇒liftA2 _<$>_ _<*>_
    ; _<*_       = MkRawApplicative.<$>,<*>⇒<* _<$>_ _<*>_
    ; _*>_       = MkRawApplicative.<$>,<*>⇒*> _<$>_ _<*>_
    ; rawFunctor = rawFunctor
    }

rawMonad : RawMonad IO
rawMonad = record
    { join            = MkRawMonad.>>=⇒join _>>=_
    ; _>>=_           = _>>=_
    ; rawIApplicative = rawApplicative
    }
