{-# OPTIONS --without-K --safe #-}

module Wna.Prelude.Computing.Instanced where

open import Wna.Class.RawFunctor using (RawFunctor)

open RawFunctor ⦃...⦄ public
    using
    ( fmap
    ; _<$>_ ; _<$_ ; _<&>_
    )

open import Wna.Class.RawFunctor.LevelPolymorphic using (RawFunctor′)

open RawFunctor′ ⦃...⦄ public
    using
    ( fmap′
    ; _<$>′_ ; _<$′_ ; _<&>′_
    )

open import Wna.Class.RawApplicative using (RawApplicative)

open RawApplicative ⦃...⦄ public
    using
    ( pure
    ; _<*>_ ; _<*_ ; _*>_
    )

open import Wna.Class.RawApplicative.LevelPolymorphic using (RawApplicative′)

open RawApplicative′ ⦃...⦄ public
    using
    ( pure′
    ; _<*>′_ ; _<*′_ ; _*>′_
    )

open import Wna.Class.RawMonad using (RawMonad)

open RawMonad ⦃...⦄ public
    using
    ( return ; join
    ; _>>=_ ; _>=>_ ; _>>_ ; _=<<_ ; _<=<_
    )

open import Wna.Class.RawMonad.LevelPolymorphic using (RawMonad′)

open RawMonad′ ⦃...⦄ public
    using
    ( return′ ; join′
    ; _>>=′_ ; _>=>′_ ; _>>′_ ; _=<<′_ ; _<=<′_
    )

--

open import Wna.Class.Monad.Trans public
    using (lift; lift′)

--

open import Wna.Class.Monad.Ask public
    using (ask; ask′)

open import Wna.Class.Monad.Handle public
    using (handle; handle′)

open import Wna.Class.Monad.Local public
    using (local; local′)

open import Wna.Class.Monad.Raise public
    using (raise; raise′)

open import Wna.Class.Monad.State public
    using (get; put; get′; put′; iget; iput; iget′; iput′)

open import Wna.Class.Monad.Tell public
    using (tell; tell′)

--

open import Wna.Class.Cast public
    using (cast)

open import Wna.Class.Foldable public
    using (foldl; foldr; is-empty; length; _∈ᵇ_)

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
