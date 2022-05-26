{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Base where

-- Extended/new data

open import Wna.Data.List public
    using  (List)
    hiding (module List)

module List = Wna.Data.List

open import Wna.Data.Vec public
    using  (Vec)
    hiding (module Vec)

module Vec = Wna.Data.Vec

open import Wna.Data.Container public
    using (Container; ⟦_⟧)
    hiding (module Container)

module Container = Wna.Data.Container

-- Classes

open import Wna.Class.RawFunctor public
    using (RawFunctor; module FunctorFT; module MkRawFunctor)

open import Wna.Class.RawApplicative public
    using
    ( RawApplicative
    ; module IApplicativeFT ; module ApplicativeFT
    ; module MkRawApplicative ; module MkRawIApplicative
    )

open import Wna.Class.RawMonad public
    using
    ( RawMonad
    ; module IMonadFT ; module MonadFT
    ; module MkRawMonad ; module MkRawIMonad
    )

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
    using  (Identity; mkIdentity; runIdentity)
    hiding (module Identity)

module Identity where
    open import Wna.Monad.Identity public

open import Wna.Monad.Maybe public
    using  (Maybe; MaybeT)
    hiding (module Maybe)

module Maybe where
    open import Wna.Monad.Maybe public

open import Wna.Monad.Except.Base public
    using (Except; ExceptT; mkExcept; runExcept)

module Except where
    open import Wna.Monad.Except public

open import Wna.Monad.Reader public
    using (Reader; ReaderT; ReaderIT; mkReader; runReader)

module Reader where
    open import Wna.Monad.Reader public

open import Wna.Monad.State.Base public
    using (State; StateT; StateI; StateTI; StateIT)
    renaming
    ( make to mkState ; run to runState
    ; eval to evalState ; exec to execState
    ; makeTI to mkStateTI ; runTI to runStateTI
    ; evalTI to evalStateTI ; execTI to execStateTI
    )

module State where
    open import Wna.Monad.State public
