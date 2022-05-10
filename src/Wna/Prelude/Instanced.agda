{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Instanced where

import Wna.Class.Monad.Trans
open Wna.Class.Monad.Trans.Instanced public
    using (lift)

import Wna.Class.Monad.Ask
open Wna.Class.Monad.Ask.Instanced public
    using (ask)

import Wna.Class.Monad.Handle
open Wna.Class.Monad.Handle.Instanced public
    using (handle)

import Wna.Class.Monad.Local
open Wna.Class.Monad.Local.Instanced public
    using (local)

import Wna.Class.Monad.Raise
open Wna.Class.Monad.Raise.Instanced public
    using (raise)

import Wna.Class.Monad.State
open Wna.Class.Monad.State.Instanced public
    using
    ( get ; put ; gets ; modify
    ; iget ; iput ; igets ; imodify
    )

import Wna.Class.Monad.Tell
open Wna.Class.Monad.Tell.Instanced public
    using (tell)

--

import Wna.Class.Cast
open Wna.Class.Cast.Instanced public
    using (cast)

import Wna.Class.Foldable
open Wna.Class.Foldable.Instanced public
    using (foldl; foldr; fold; foldMap)

import Wna.Class.Numeric
open Wna.Class.Numeric.Instanced public
    using
    ( -_ ; _+_ ; _-_ ; _*_ ; _/_
    ; _%_ ; _quot_; _rem_ ; _^_
    ; _² ; 1/_
    ; exp ; abs
    ; _∨_ ; _∧_
    )

import Wna.Class.RawEquality
open Wna.Class.RawEquality.Instanced public
    using (_≡ᵇ_; _≢ᵇ_)

import Wna.Class.RawOrder
open Wna.Class.RawOrder.Instanced public
    using
    ( _<ᵇ_ ; _>ᵇ_ ; _≮ᵇ_ ; _≯ᵇ_
    ; _≤ᵇ_ ; _≥ᵇ_ ; _≱ᵇ_ ; _≰ᵇ_
    )

--

import Wna.Class.DecEquality
open Wna.Class.DecEquality.Instanced public
    using (_≈?_; _≡?_)

import Wna.Class.DecOrder
open Wna.Class.DecOrder.Instanced public
    using (_<?_; _>?_; _≤?_; _≥?_)
