{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Base where

open import Wna.Monad.Identity public
    using (Identity; mkIdentity; runIdentity)

open import Wna.Monad.Maybe public
    using (Maybe; MaybeT; MaybeT′)

open import Wna.Monad.Except public
    using (Except; ExceptT; mkExcept; runExcept)

open import Wna.Monad.Reader public
    using (Reader; ReaderT; ReaderIT; mkReader; runReader)

open import Wna.Monad.State public
    using (IState; State; StateT; StateIT; StateTI; mkState; runState)
