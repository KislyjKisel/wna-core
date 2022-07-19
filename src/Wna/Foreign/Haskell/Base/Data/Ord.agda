{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Base.Data.Ord where

open import Data.Bool.Base                                 using (Bool)
open import Data.Product                                   using (_×_)
open import Foreign.Haskell.Coerce                         using (coerce)
open import Foreign.Haskell.Pair                           using (Pair)
open import Wna.Data.Ordering.Base                         using (Ordering)
open import Wna.Foreign.Haskell.Base.Data.Ordering as HOrd using ()         renaming (Ordering to HsOrdering)
open import Wna.Primitive

postulate
    Ord : ∀{ℓ} → Type ℓ → Type ℓ

{-# FOREIGN GHC import qualified Data.Ord #-}

{-# FOREIGN GHC data AgdaOrdDict a b = Ord b => AgdaOrdDict #-}
{-# COMPILE GHC Ord = type AgdaOrdDict #-}

infix 4 _<_ _<=_ _>_ _>=_

postulate
    _<_  : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → Bool
    _<=_ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → Bool
    _>_  : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → Bool
    _>=_ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → Bool

    compare : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → HsOrdering
    min     : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → A
    max     : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → A

    comparing : ∀{ℓ} {A B : Type ℓ} ⦃ _ : Ord A ⦄ → (B → A) → B → B → HsOrdering
    clamp     : ∀{ℓ} {A   : Type ℓ} ⦃ _ : Ord A ⦄ → Pair A A → A → A

compare′ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A → A → Ordering
compare′ x y = HOrd.fromForeign (compare x y)

comparing′ : ∀{ℓ} {A B : Type ℓ} ⦃ _ : Ord A ⦄ → (B → A) → B → B → Ordering
comparing′ f x y = HOrd.fromForeign (comparing f x y)

clamp′ : ∀{ℓ} {A : Type ℓ} ⦃ _ : Ord A ⦄ → A × A → A → A
clamp′ p = clamp (coerce p)

-- todo: postulated properties?

{-# COMPILE GHC _<_  = \ ℓ a AgdaOrdDict -> (<)  #-}
{-# COMPILE GHC _<=_ = \ ℓ a AgdaOrdDict -> (<=) #-}
{-# COMPILE GHC _>_  = \ ℓ a AgdaOrdDict -> (>)  #-}
{-# COMPILE GHC _>=_ = \ ℓ a AgdaOrdDict -> (>=) #-}

{-# COMPILE GHC compare = \ ℓ a AgdaOrdDict -> compare #-}
{-# COMPILE GHC min     = \ ℓ a AgdaOrdDict -> min #-}
{-# COMPILE GHC max     = \ ℓ a AgdaOrdDict -> max #-}

{-# COMPILE GHC comparing = \ ℓ a b AgdaOrdDict -> Data.Ord.comparing #-}
{-# COMPILE GHC clamp     = \ ℓ a   AgdaOrdDict -> Data.Ord.clamp     #-}
