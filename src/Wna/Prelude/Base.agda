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
    renaming (Trans to MonadTrans)
    using ()

open import Wna.Class.Monad.Ask public
    renaming (Ask to MonadAsk)
    using ()

open import Wna.Class.Monad.Handle public
    renaming (Handle to MonadHandle)
    using ()

open import Wna.Class.Monad.Local public
    renaming (Local to MonadLocal)
    using ()

open import Wna.Class.Monad.Raise public
    renaming (Raise to MonadRaise)
    using ()

open import Wna.Class.Monad.State public
    renaming (State to MonadState)
    using ()

open import Wna.Class.Monad.Tell public
    renaming (Tell to MonadTell)
    using ()

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
