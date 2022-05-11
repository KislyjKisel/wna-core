{-# OPTIONS --without-K --safe #-}

module Wna.Class.Traversable where

open import Function.Base                     using (const; id; _$_; _∘′_)
open import Wna.Class.RawFunctor              using (RawFunctor; module FunctorFT)
open import Wna.Class.RawApplicative          using (RawApplicative; module MkRawApplicative)
open import Wna.Class.RawMonad                using (RawMonad)
open import Wna.Class.RawMonoid               using (RawMonoid)
open import Wna.Monad.Identity        as Id   using (Identity; mkIdentity; runIdentity)
open import Wna.Monad.Unit            as Unit using (Unit; mkUnit; runUnit)
open import Wna.Primitive

-- not superclass of Foldable currently, because I don't know how to make foldable from traversable

module _ {ℓ} (T : Type ℓ → Type ℓ) where
    module TraversableFT where
        open FunctorFT T public

        traverse = ∀{A B} {F : Type ℓ → Type ℓ} ⦃ _ : RawApplicative F ⦄ →
            (A → F B) → T A → F (T B)
        
        sequenceA = ∀{A} {F : Type ℓ → Type ℓ} ⦃ _ : RawApplicative F ⦄ →
            T (F A) → F (T A)
        
        mapM = ∀{A B} {M : Type ℓ → Type ℓ} ⦃ _ : RawMonad M ⦄ →
            (A → M B) → T A → M (T B)
        
        sequence = ∀{A} {M : Type ℓ → Type ℓ} ⦃ _ : RawMonad M ⦄ →
            T (M A) → M (T A)

    record Traversable : Typeω where
        field
            overlap ⦃ rawFunctor ⦄ : RawFunctor T

            traverse  : TraversableFT.traverse
            sequenceA : TraversableFT.sequenceA
            mapM      : TraversableFT.mapM
            sequence  : TraversableFT.sequence

    module MkTraversable where

        traverse⇒mapM : TraversableFT.traverse → TraversableFT.mapM
        traverse⇒mapM traverse = traverse

        traverse⇒sequence : TraversableFT.traverse → TraversableFT.sequence
        traverse⇒sequence = _$ id

        traverse⇒sequenceA : TraversableFT.traverse → TraversableFT.sequenceA
        traverse⇒sequenceA = _$ id

        traverse⇒map : TraversableFT.traverse → TraversableFT.map
        traverse⇒map traverse f = runIdentity ∘′ (traverse {F = Identity} ⦃ Id.rawApplicative ⦄ $ mkIdentity ∘′ f)

        traverse⇒foldMap' : TraversableFT.traverse →
            {A B : Type ℓ} → ⦃ _ : RawMonoid B ⦄ → (A → B) → T A → B
        traverse⇒foldMap' traverse {B = B} ⦃ B-rawMonoid ⦄ f x = traverse {B = B} f x
            where
            module B = RawMonoid B-rawMonoid
            instance
                _ : RawApplicative (const B)
                _ = MkRawApplicative.from:pure,<*> (const B.mempty) B.mappend

        sequenceA⇒traverse : ⦃ _ : RawFunctor T ⦄ → TraversableFT.sequenceA → TraversableFT.traverse
        sequenceA⇒traverse ⦃ T-rawFunctor ⦄ sequenceA ⦃ F-rawApplicative ⦄ f = sequenceA ∘′ T.map f
            where module T = RawFunctor T-rawFunctor

        sequenceA⇒sequence : TraversableFT.sequenceA → TraversableFT.sequence
        sequenceA⇒sequence sequenceA = sequenceA

        sequenceA⇒mapM : ⦃ _ : RawFunctor T ⦄ → TraversableFT.sequenceA → TraversableFT.mapM
        sequenceA⇒mapM sequenceA = sequenceA⇒traverse sequenceA

        from:traverse′ : ⦃ _ : RawFunctor T ⦄ → TraversableFT.traverse → Traversable
        from:traverse′ traverse = record
            { traverse   = traverse
            ; sequenceA  = traverse⇒sequenceA traverse
            ; mapM       = traverse⇒mapM traverse
            ; sequence   = traverse⇒sequence traverse
            }

        from:sequenceA′ : ⦃ _ : RawFunctor T ⦄ → TraversableFT.sequenceA → Traversable
        from:sequenceA′ sequenceA = record
            { traverse  = sequenceA⇒traverse sequenceA
            ; sequenceA = sequenceA
            ; mapM      = sequenceA⇒mapM sequenceA
            ; sequence  = sequenceA⇒sequence sequenceA
            }
