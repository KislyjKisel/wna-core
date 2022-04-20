{-# OPTIONS --without-K --safe #-}

module Wna.Class.Monoid where

record Monoid {mℓ} (M : Set mℓ) : Set mℓ where
    field
        ε    : M
        _<>_ : M → M → M

open Monoid ⦃...⦄ public

record Endo {aℓ} (A : Set aℓ) : Set aℓ where
    constructor mkEndo
    field
        appEndo : A → A

open Endo public

record Dual {aℓ} (A : Set aℓ) : Set aℓ where
    constructor mkDual
    field
        getDual : A

open Dual public
