{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Instanced where

open import Wna.Class.RawFunctor.Instanced      public
open import Wna.Class.RawApplicative.Instanced  public
open import Wna.Class.RawMonad.Instanced        public

--

open import Wna.Class.Monad.Trans public
    using (lift)

open import Wna.Class.Monad.Ask public
    using (ask)

open import Wna.Class.Monad.Handle public
    using (handle)

open import Wna.Class.Monad.Local public
    using (local)

open import Wna.Class.Monad.Raise public
    using (raise)

open import Wna.Class.Monad.State public
    using
    ( get ; put ; gets ; modify
    ; iget ; iput ; igets ; imodify
    )

open import Wna.Class.Monad.Tell public
    using (tell)

--

open import Wna.Class.Cast public
    using (cast)

open import Wna.Class.Foldable public
    using (foldl; foldr; fold; foldMap)

open import Wna.Class.Numeric public
    using
    ( -_ ; _+_ ; _-_ ; _*_ ; _/_
    ; _%_ ; _quot_; _rem_ ; _^_
    ; _² ; 1/_
    ; exp ; abs
    ; _∨_ ; _∧_
    )

open import Wna.Class.RawEquality public
    using (_≡ᵇ_; _≢ᵇ_)

open import Wna.Class.RawOrder public
    using
    ( _<ᵇ_ ; _>ᵇ_ ; _≮ᵇ_ ; _≯ᵇ_
    ; _≤ᵇ_ ; _≥ᵇ_ ; _≱ᵇ_ ; _≰ᵇ_
    )

--

open import Wna.Class.DecEquality public
    using (_≈?_; _≡?_)

open import Wna.Class.DecOrder public
    using (_<?_; _>?_; _≤?_; _≥?_)
