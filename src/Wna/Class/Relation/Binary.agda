{-# OPTIONS --without-K --safe #-}

module Wna.Class.Relation.Binary where

open import Data.Bool.Base                             using (Bool; not)
open import Data.Product                               using (proj₁; proj₂)
open import Function.Base                              using (_∘₂′_; _∘₂_; flip)
open import Level                                 as ℓ using (Level)
open import Relation.Binary.Consequences               using (trans∧irr⇒asym)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Relation.Binary.Structures
open import Relation.Nullary.Decidable                 using (isYes)
open import Relation.Nullary.Negation                  using (¬_)

private
    variable
        aℓ ≈ℓ ≤ℓ <ℓ #ℓ : Level
        A : Set aℓ


record RawSetoid ≈ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ) where
    infix 4 _≈_ _≉_
    field
        _≈_ : Rel A ≈ℓ

    _≉_ : Rel A ≈ℓ
    _≉_ = ¬_ ∘₂′ _≈_

record PartialSetoid ≈ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ) where
    field
        overlap ⦃ rawSetoid ⦄ : RawSetoid ≈ℓ A

    open RawSetoid rawSetoid public

    field
        ≈-sym   : Symmetric _≈_
        ≈-trans : Transitive _≈_

record Setoid ≈ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ) where
    field
        overlap ⦃ partialSetoid ⦄ : PartialSetoid ≈ℓ A

    open PartialSetoid partialSetoid public

    field
        ≈-refl : Reflexive _≈_

    ≈-reflexive : _≡_ ⇒ _≈_
    ≈-reflexive ≡.refl = ≈-refl

record DecSetoidᵇ (A : Set aℓ) : Set aℓ where
    infix 4 _≈ᵇ_ _≉ᵇ_
    field
        _≈ᵇ_ : A → A → Bool

    _≉ᵇ_ : A → A → Bool
    _≉ᵇ_ = not ∘₂′ _≈ᵇ_

record DecSetoid ≈ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ) where
    field
        overlap ⦃ rawSetoid  ⦄ : RawSetoid ≈ℓ A
        overlap ⦃ decSetoidᵇ ⦄ : DecSetoidᵇ A

    open RawSetoid  rawSetoid  public
    open DecSetoidᵇ decSetoidᵇ public

    infix 4 _≈?_
    field
        _≈?_ : Decidable _≈_

        ≈?⇔≈ᵇ : ∀{x y} → (isYes (x ≈? y)) ≡ (x ≈ᵇ y)

record RawOrder ≤ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≤ℓ) where
    infix 4 _≤_ _≥_ _≯_ _≮_
    field
        _≤_ : Rel A ≤ℓ

    _≥_ = flip _≤_
    _≯_ = _≤_
    _≮_ = _≥_

record DecOrderᵇ (A : Set aℓ) : Set aℓ where
    infix 4 _≤ᵇ_ _≥ᵇ_ _≯ᵇ_ _≮ᵇ_
    field
        _≤ᵇ_ : A → A → Bool

    _≥ᵇ_ = flip _≤ᵇ_
    _≯ᵇ_ = _≤ᵇ_
    _≮ᵇ_ = _≥ᵇ_

record DecOrder ≤ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≤ℓ) where
    field
        overlap ⦃ rawOrder  ⦄ : RawOrder ≤ℓ A
        overlap ⦃ decOrderᵇ ⦄ : DecOrderᵇ A

    open RawOrder  rawOrder  public
    open DecOrderᵇ decOrderᵇ public

    infix 4 _≤?_ _≥?_ _≯?_ _≮?_
    field
        _≤?_ : Decidable _≤_

        ≤?⇔≤ᵇ : ∀{x y} → (isYes (x ≤? y)) ≡ (x ≤ᵇ y)

    _≥?_ = flip _≤?_
    _≯?_ = _≤?_
    _≮?_ = _≥?_

record Poset ≈ℓ ≤ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ ℓ.⊔ ℓ.suc ≤ℓ) where
    field
        overlap ⦃ setoid   ⦄ : Setoid ≈ℓ A
        overlap ⦃ rawOrder ⦄ : RawOrder ≤ℓ A

    open Setoid   setoid   public
    open RawOrder rawOrder public

    field
        ≈⇒≤       : _≈_ ⇒ _≤_
        ≤-trans   : Transitive _≤_
        ≤-antisym : Antisymmetric _≈_ _≤_

record TotalOrder ≈ℓ ≤ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ ℓ.⊔ ℓ.suc ≤ℓ) where
    field
        overlap ⦃ poset ⦄ : Poset ≈ℓ ≤ℓ A

    open Poset poset public

    field
        ≤-total : Total _≤_

record RawStrictOrder <ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc <ℓ) where
    infix 4 _<_ _>_ _≱_ _≰_
    field
        _<_ : Rel A <ℓ

    _>_ = flip _<_
    _≱_ = _<_
    _≰_ = _>_

record DecStrictOrderᵇ (A : Set aℓ) : Set aℓ where
    infix 4 _<ᵇ_ _>ᵇ_ _≱ᵇ_ _≰ᵇ_
    field
        _<ᵇ_ : A → A → Bool

    _>ᵇ_ = flip _<ᵇ_
    _≱ᵇ_ = _<ᵇ_
    _≰ᵇ_ = _>ᵇ_

record DecStrictOrder <ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc <ℓ) where
    field
        overlap ⦃ rawStrictOrder  ⦄ : RawStrictOrder <ℓ A
        overlap ⦃ decStrictOrderᵇ ⦄ : DecStrictOrderᵇ A

    open RawStrictOrder  rawStrictOrder  public
    open DecStrictOrderᵇ decStrictOrderᵇ public

    infix 4 _<?_ _>?_ _≱?_ _≰?_
    field
        _<?_ : Decidable _<_

        <?⇔<ᵇ : ∀{x y} → (isYes (x <? y)) ≡ (x <ᵇ y)

    _>?_ = flip _<?_
    _≱?_ = _<?_
    _≰?_ = _>?_

record StrictPartialOrder ≈ℓ <ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ ℓ.⊔ ℓ.suc <ℓ) where
    field
        overlap ⦃ setoid         ⦄ : Setoid ≈ℓ A
        overlap ⦃ rawStrictOrder ⦄ : RawStrictOrder <ℓ A

    open Setoid         setoid         public
    open RawStrictOrder rawStrictOrder public

    field
        <-trans   : Transitive _<_
        <-irrefl  : Irreflexive _≈_ _<_
        <-resp-≈  : _<_ Respects₂ _≈_

    <-asym : Asymmetric _<_
    <-asym {x} {y} = trans∧irr⇒asym ≈-refl <-trans <-irrefl {x = x} {y}

    <-respʳ-≈ : _<_ Respectsʳ _≈_
    <-respʳ-≈ = proj₁ <-resp-≈

    <-respˡ-≈ : _<_ Respectsˡ _≈_
    <-respˡ-≈ = proj₂ <-resp-≈

record StrictTotalOrder ≈ℓ <ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ ℓ.⊔ ℓ.suc <ℓ) where
    field
        overlap ⦃ strictPartialOrder ⦄ : StrictPartialOrder ≈ℓ <ℓ A
        overlap ⦃ decStrictOrder     ⦄ : DecStrictOrder <ℓ A
        coherent : StrictPartialOrder.rawStrictOrder strictPartialOrder ≡ DecStrictOrder.rawStrictOrder decStrictOrder

    open StrictPartialOrder strictPartialOrder public
    open DecStrictOrder     decStrictOrder     public
        hiding (rawStrictOrder; _<_; _>_; _≱_; _≰_)

    field
        <-compare : Trichotomous _≈_ _<_


record RawApart #ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc #ℓ) where
    infix 4 _#_ _¬#_
    field
        _#_ : Rel A #ℓ

    _¬#_ : Rel A #ℓ
    _¬#_ = ¬_ ∘₂′ _#_

record Apart ≈ℓ #ℓ (A : Set aℓ) : Set (aℓ ℓ.⊔ ℓ.suc ≈ℓ ℓ.⊔ ℓ.suc #ℓ) where
    field
        overlap ⦃ setoid   ⦄ : Setoid ≈ℓ A
        overlap ⦃ rawApart ⦄ : RawApart #ℓ A

    open Setoid   setoid   public
    open RawApart rawApart public

    field
        #-irrefl  : Irreflexive _≈_ _#_
        #-sym     : Symmetric _#_
        #-cotrans : Cotransitive _#_


module From where
    module Structures where

        partialSetoid : ∀{_≈_ : Rel A ≈ℓ} → IsPartialEquivalence _≈_ → PartialSetoid ≈ℓ A
        partialSetoid {_≈_ = _≈_} s = record
            { rawSetoid = record { _≈_ = _≈_ }
            ; ≈-sym     = IsPartialEquivalence.sym s
            ; ≈-trans   = IsPartialEquivalence.trans s
            }

        setoid : ∀{_≈_ : Rel A ≈ℓ} → IsEquivalence _≈_ → Setoid ≈ℓ A
        setoid s = record
            { partialSetoid = partialSetoid (IsEquivalence.isPartialEquivalence s)
            ; ≈-refl = IsEquivalence.refl s
            }

    module Bundles where
        import Relation.Binary.Bundles as Std

        partialSetoid : (b : Std.PartialSetoid aℓ ≈ℓ) → PartialSetoid ≈ℓ (Std.PartialSetoid.Carrier b)
        partialSetoid b = record
            { rawSetoid = record { _≈_ = _≈_ }
            ; ≈-sym     = sym
            ; ≈-trans   = trans
            }
            where open Std.PartialSetoid b

        setoid : (b : Std.Setoid aℓ ≈ℓ) → Setoid ≈ℓ (Std.Setoid.Carrier b)
        setoid b = record
            { partialSetoid = partialSetoid (Std.Setoid.partialSetoid b)
            ; ≈-refl        = Std.Setoid.refl b
            }

        decSetoidᵇ : (b : Std.DecSetoid aℓ ≈ℓ) → DecSetoidᵇ (Std.DecSetoid.Carrier b)
        decSetoidᵇ b = record
            { _≈ᵇ_ = isYes ∘₂ Std.DecSetoid._≟_ b
            }

        decSetoid : (b : Std.DecSetoid aℓ ≈ℓ) → DecSetoid ≈ℓ (Std.DecSetoid.Carrier b)
        decSetoid b = record
            { rawSetoid  = record { _≈_ = Std.DecSetoid._≈_ b }
            ; decSetoidᵇ = decSetoidᵇ b
            ; _≈?_       = Std.DecSetoid._≟_ b
            ; ≈?⇔≈ᵇ      = ≡.refl
            }

        decOrderᵇ : (b : Std.DecPoset aℓ ≈ℓ ≤ℓ) → DecOrderᵇ (Std.DecPoset.Carrier b)
        decOrderᵇ b = record
            { _≤ᵇ_ = isYes ∘₂ Std.DecPoset._≤?_ b
            }

        decOrder : (b : Std.DecPoset aℓ ≈ℓ ≤ℓ) → DecOrder ≤ℓ (Std.DecPoset.Carrier b)
        decOrder b = record
            { rawOrder  = record { _≤_ = Std.DecPoset._≤_ b }
            ; decOrderᵇ = decOrderᵇ b
            ; _≤?_      = Std.DecPoset._≤?_ b
            ; ≤?⇔≤ᵇ     = ≡.refl
            }

        poset : (b : Std.Poset aℓ ≈ℓ ≤ℓ) → Poset ≈ℓ ≤ℓ (Std.Poset.Carrier b)
        poset b = record
            { setoid    = setoid (Std.Poset.Eq.setoid b)
            ; rawOrder  = record { _≤_ = Std.Poset._≤_ b }
            ; ≈⇒≤       = Std.Poset.reflexive b
            ; ≤-trans   = Std.Poset.trans b
            ; ≤-antisym = Std.Poset.antisym b
            }

        totalOrder : (b : Std.TotalOrder aℓ ≈ℓ ≤ℓ) → TotalOrder ≈ℓ ≤ℓ (Std.TotalOrder.Carrier b)
        totalOrder b = record
            { poset   = poset (Std.TotalOrder.poset b)
            ; ≤-total = Std.TotalOrder.total b
            }

        decStrictOrderᵇ : (b : Std.DecStrictPartialOrder aℓ ≈ℓ <ℓ) → DecStrictOrderᵇ (Std.DecStrictPartialOrder.Carrier b)
        decStrictOrderᵇ b = record
            { _<ᵇ_ = isYes ∘₂ Std.DecStrictPartialOrder._<?_ b
            }

        decStrictOrderᵇ′ : (b : Std.StrictTotalOrder aℓ ≈ℓ <ℓ) → DecStrictOrderᵇ (Std.StrictTotalOrder.Carrier b)
        decStrictOrderᵇ′ b = record
            { _<ᵇ_ = isYes ∘₂ Std.StrictTotalOrder._<?_ b
            }

        decStrictOrder : (b : Std.DecStrictPartialOrder aℓ ≈ℓ <ℓ) → DecStrictOrder <ℓ (Std.DecStrictPartialOrder.Carrier b)
        decStrictOrder b = record
            { rawStrictOrder  = record { _<_ = Std.DecStrictPartialOrder._<_ b }
            ; decStrictOrderᵇ = decStrictOrderᵇ b
            ; _<?_            = Std.DecStrictPartialOrder._<?_ b
            ; <?⇔<ᵇ           = ≡.refl
            }

        decStrictOrder′ : (b : Std.StrictTotalOrder aℓ ≈ℓ <ℓ) → DecStrictOrder <ℓ (Std.StrictTotalOrder.Carrier b)
        decStrictOrder′ b = record
            { rawStrictOrder  = record { _<_ = Std.StrictTotalOrder._<_ b }
            ; decStrictOrderᵇ = decStrictOrderᵇ′ b
            ; _<?_            = Std.StrictTotalOrder._<?_ b
            ; <?⇔<ᵇ           = ≡.refl
            }

        strictPartialOrder : (b : Std.StrictPartialOrder aℓ ≈ℓ <ℓ) → StrictPartialOrder ≈ℓ <ℓ (Std.StrictPartialOrder.Carrier b)
        strictPartialOrder b = record
            { setoid         = setoid (Std.StrictPartialOrder.Eq.setoid b)
            ; rawStrictOrder = record { _<_ = Std.StrictPartialOrder._<_ b }
            ; <-trans        = Std.StrictPartialOrder.trans b
            ; <-irrefl       = Std.StrictPartialOrder.irrefl b
            ; <-resp-≈       = Std.StrictPartialOrder.<-resp-≈ b
            }

        strictTotalOrder : (b : Std.StrictTotalOrder aℓ ≈ℓ <ℓ) → StrictTotalOrder ≈ℓ <ℓ (Std.StrictTotalOrder.Carrier b)
        strictTotalOrder b = record
            { strictPartialOrder = strictPartialOrder (Std.StrictTotalOrder.strictPartialOrder b)
            ; decStrictOrder     = decStrictOrder′ b
            ; coherent           = ≡.refl
            ; <-compare          = Std.StrictTotalOrder.compare b
            }

        apart : (b : Std.ApartnessRelation aℓ ≈ℓ #ℓ) → IsEquivalence (Std.ApartnessRelation._≈_ b) → Apart ≈ℓ #ℓ (Std.ApartnessRelation.Carrier b)
        apart b ≈-isEq = record
            { setoid    = Structures.setoid ≈-isEq
            ; rawApart  = record { _#_ = Std.ApartnessRelation._#_ b }
            ; #-irrefl  = Std.ApartnessRelation.irrefl b
            ; #-sym     = Std.ApartnessRelation.sym b
            ; #-cotrans = Std.ApartnessRelation.cotrans b
            }

module Instanced where
    open RawSetoid ⦃...⦄ public
        using (_≈_)

    open PartialSetoid ⦃...⦄ public
        using (≈-sym; ≈-trans)

    open Setoid ⦃...⦄ public
        using (≈-refl)

    open DecSetoidᵇ ⦃...⦄ public
        using (_≈ᵇ_; _≉ᵇ_)

    open DecSetoid ⦃...⦄ public
        using (_≈?_)

    open RawOrder ⦃...⦄ public
        using (_≤_; _≥_; _≯_; _≮_)

    open DecOrderᵇ ⦃...⦄ public
        using (_≤ᵇ_; _≥ᵇ_; _≯ᵇ_; _≮ᵇ_)

    open DecOrder ⦃...⦄ public
        using (_≤?_; _≥?_; _≯?_; _≮?_)

    open Poset ⦃...⦄ public
        using (≈⇒≤; ≤-trans; ≤-antisym)

    open TotalOrder ⦃...⦄ public
        using (≤-total)

    open RawStrictOrder ⦃...⦄ public
        using (_<_; _>_; _≱_; _≰_)

    open DecStrictOrderᵇ ⦃...⦄ public
        using (_<ᵇ_; _>ᵇ_; _≱ᵇ_; _≰ᵇ_)

    open DecStrictOrder ⦃...⦄ public
        using (_<?_; _>?_; _≱?_; _≰?_)

    open StrictPartialOrder ⦃...⦄ public
        using (<-trans; <-irrefl; <-asym; <-resp-≈; <-respʳ-≈; <-respˡ-≈)

    open StrictTotalOrder ⦃...⦄ public
        using (<-compare)

    open RawApart ⦃...⦄ public
        using (_#_; _¬#_)

    open Apart ⦃...⦄ public
        using (#-irrefl; #-sym; #-cotrans)
