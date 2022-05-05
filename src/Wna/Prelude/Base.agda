{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Base where

-- Classes

open import Wna.Class.RawFunctor public
    using (RawFunctor)

open import Wna.Class.RawApplicative public
    using (RawApplicative)

open import Wna.Class.RawMonad public
    using (RawMonad)

open import Wna.Class.Cast public
    using (Cast[_⇒_])

open import Wna.Class.Foldable public
    using (Foldable)

open import Wna.Class.RawEquality public
    using (RawEquality)

open import Wna.Class.DecEquality public
    using (DecEquality)

open import Wna.Class.RawMonoid public
    using (RawMonoid)

open import Wna.Class.RawOrder public
    using (RawStrictOrder; RawOrder)

open import Wna.Class.DecOrder public
    using (DecOrder)

-- Monad classes

open import Wna.Class.Monad.Trans public
    using (MonadTrans)

open import Wna.Class.Monad.Ask public
    using (MonadAsk)

open import Wna.Class.Monad.Handle public
    using (MonadHandle)

open import Wna.Class.Monad.Local public
    using (MonadLocal)

open import Wna.Class.Monad.Raise public
    using (MonadRaise)

open import Wna.Class.Monad.State public
    using (MonadState; IMonadState)

open import Wna.Class.Monad.Tell public
    using (MonadTell)

-- Monads

open import Wna.Monad.Identity public
    using (Identity; mkIdentity; runIdentity)

open import Wna.Monad.Maybe public
    using (Maybe; MaybeT)

open import Wna.Monad.Except public
    using (Except; ExceptT; mkExcept; runExcept)

open import Wna.Monad.Reader public
    using (Reader; ReaderT; ReaderIT; mkReader; runReader)

open import Wna.Monad.State public
    using
    ( IState ; State ; StateT ; StateIT ; StateTI ; mkState
    ; runState ; evalState ; execState
    ; runState′ ; evalState′ ; execState′
    )
