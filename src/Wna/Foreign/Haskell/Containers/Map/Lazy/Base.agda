{-# OPTIONS --without-K #-}

module Wna.Foreign.Haskell.Containers.Map.Lazy.Base where

open import Data.List.Base                     as List using (List)
open import Data.Maybe.Base                            using (Maybe)
open import Data.Product                       as Σ    using (_×_)
open import Data.Tree.AVL.Map                  as Safe using ()
open import Foreign.Haskell.Coerce                     using (coerce)
open import Foreign.Haskell.Pair                       using (Pair)
open import Function.Base                              using (_$_; _∘′_)
open import Relation.Binary.Bundles                    using (StrictTotalOrder)
open import Wna.Foreign.Haskell.Base.Class.Ord         using (Ord)
open import Wna.Primitive

{-# FOREIGN GHC import qualified Data.Map.Lazy #-}
{-# FOREIGN GHC import MAlonzo.Code.Wna.Foreign.Haskell.Base.Class.Ord (AgdaOrdDict(AgdaOrdDict)) #-}

postulate
    Map : ∀{kℓ vℓ} → (K : Type kℓ) → (V : Type vℓ) → Type (kℓ ℓ⊔ vℓ)

    -- Construction
    empty     : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} →         Map K V
    singleton : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → K → V → Map K V

    fromList  : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ → List (Pair K V) → Map K V 

    -- Insertion
    insert     : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ →               K → V → Map K V → Map K V
    insertWith : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ → (V → V → V) → K → V → Map K V → Map K V

    -- Update
    delete : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ →                       K → Map K V → Map K V
    adjust : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ → (      V →       V) → K → Map K V → Map K V
    update : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ → (      V → Maybe V) → K → Map K V → Map K V
    alter  : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → ⦃ _ : Ord K ⦄ → (Maybe V → Maybe V) → K → Map K V → Map K V

    -- Folds
    foldr        : ∀{kℓ vℓ bℓ} {K : Type kℓ} {V : Type vℓ} {B : Type bℓ} → (    V → B → B) → B → Map K V → B
    foldrWithKey : ∀{kℓ vℓ bℓ} {K : Type kℓ} {V : Type vℓ} {B : Type bℓ} → (K → V → B → B) → B → Map K V → B

    -- Conversion
    toList : ∀{kℓ vℓ} {K : Type kℓ} {V : Type vℓ} → Map K V → List (Pair K V)

toForeign : ∀{kℓ k≈ℓ k<ℓ vℓ} {o : StrictTotalOrder kℓ k≈ℓ k<ℓ} ⦃ _ : Ord (StrictTotalOrder.Carrier o) ⦄ {V : Type vℓ} → Safe.Map o V → Map (StrictTotalOrder.Carrier o) V
toForeign {o = o} = Safe.foldr o insert empty

fromForeign : ∀{kℓ k≈ℓ k<ℓ vℓ} {o : StrictTotalOrder kℓ k≈ℓ k<ℓ} {V : Type vℓ} → Map (StrictTotalOrder.Carrier o) V → Safe.Map o V 
fromForeign {o = o} = foldrWithKey (Safe.insert o) (Safe.empty o)

toForeignKV : ∀{kℓ k'ℓ k'≈ℓ k'<ℓ vℓ v'ℓ} {K : Type kℓ} {o : StrictTotalOrder k'ℓ k'≈ℓ k'<ℓ} ⦃ _ : Ord K ⦄ {V : Type vℓ} {V' : Type v'ℓ} → (StrictTotalOrder.Carrier o × V → K × V') → Safe.Map o V → Map K V'
toForeignKV {o = o} f = fromList ∘′ List.map (coerce ∘′ f) ∘′ Safe.toList o

fromForeignKV : ∀{kℓ k'ℓ k'≈ℓ k'<ℓ vℓ v'ℓ} {K : Type kℓ} {o : StrictTotalOrder k'ℓ k'≈ℓ k'<ℓ} ⦃ _ : Ord K ⦄ {V : Type vℓ} {V' : Type v'ℓ} → (K × V → StrictTotalOrder.Carrier o × V') → Map K V → Safe.Map o V'
fromForeignKV {o = o} f = Safe.fromList o ∘′ List.map (f ∘′ coerce) ∘′ toList

toForeignK : ∀{kℓ k'ℓ k'≈ℓ k'<ℓ vℓ} {K : Type kℓ} {o : StrictTotalOrder k'ℓ k'≈ℓ k'<ℓ} ⦃ _ : Ord K ⦄ {V : Type vℓ} → (StrictTotalOrder.Carrier o → K) → Safe.Map o V → Map K V
toForeignK {o = o} k = toForeignKV $ Σ.map₁ k

fromForeignK : ∀{kℓ k'ℓ k'≈ℓ k'<ℓ vℓ} {K : Type kℓ} {o : StrictTotalOrder k'ℓ k'≈ℓ k'<ℓ} ⦃ _ : Ord K ⦄ {V : Type vℓ} → (K → StrictTotalOrder.Carrier o) → Map K V → Safe.Map o V
fromForeignK {o = o} k = fromForeignKV $ Σ.map₁ k

{-# FOREIGN GHC type AgdaMap kℓ vℓ = Data.Map.Lazy.Map #-}
{-# COMPILE GHC Map = type AgdaMap #-}

{-# COMPILE GHC empty        = \ kℓ vℓ    k v               -> Data.Map.Lazy.empty        #-}
{-# COMPILE GHC singleton    = \ kℓ vℓ    k v               -> Data.Map.Lazy.singleton    #-}
{-# COMPILE GHC fromList     = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.fromList     #-}
{-# COMPILE GHC insert       = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.insert       #-}
{-# COMPILE GHC insertWith   = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.insertWith   #-}
{-# COMPILE GHC delete       = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.delete       #-}
{-# COMPILE GHC adjust       = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.adjust       #-}
{-# COMPILE GHC update       = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.update       #-}
{-# COMPILE GHC alter        = \ kℓ vℓ    k v   AgdaOrdDict -> Data.Map.Lazy.alter        #-}
{-# COMPILE GHC foldr        = \ kℓ vℓ bℓ k v b             -> Data.Map.Lazy.foldr        #-}
{-# COMPILE GHC foldrWithKey = \ kℓ vℓ bℓ k v b             -> Data.Map.Lazy.foldrWithKey #-}
{-# COMPILE GHC toList       = \ kℓ vℓ    k v               -> Data.Map.Lazy.toList       #-}
