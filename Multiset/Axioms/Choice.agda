{-# OPTIONS --safe #-}

module Multiset.Axioms.Choice where

open import Multiset.Prelude

open import Cubical.Data.Sigma.Base

open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

--- The Axiom of Choice
AC : (ℓA ℓB ℓR : Level) → Type (ℓ-suc (ℓ-max ℓA (ℓ-max ℓB ℓR)))
AC ℓA ℓB ℓR =
  ∀ {A : Type ℓA} {B : A → Type ℓB}
  → (R : (a : A) → (B a) → Type ℓR)
  → isSet A
  → (∀ a → isSet (B a))
  → (∀ a b → isProp (R a b))
  → (∀ a → ∥ Σ[ b ∈ B a ] R a b ∥₁)
  → ∥ Σ[ f ∈ ((a : A) → B a) ] (∀ a → R a (f a)) ∥₁

module _ {ℓA ℓB ℓR : Level} {A : Type ℓA} {B : A → Type ℓB}
  (R : (a : A) → (B a) → Type ℓR)
  (setA : isSet A)
  (setB : ∀ a → isSet (B a))
  (propR : ∀ a b → isProp (R a b))
  where

  hasAC : Type _
  hasAC = (∀ a → ∥ Σ[ b ∈ B a ] R a b ∥₁) → ∥ Σ[ f ∈ ((a : A) → B a) ] (∀ a → R a (f a)) ∥₁
