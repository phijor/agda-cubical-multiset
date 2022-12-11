{-# OPTIONS --sized-types #-}

module Multiset.Coinductive where

open import Multiset.Prelude
open import Multiset.Coinductive.FinCoalg
open import Multiset.Coinductive.Trees
open import Multiset.Coinductive.Setoid

private
  open import Cubical.Foundations.Equiv using (_≃_)
  open import Cubical.Foundations.Isomorphism using (section)
  open import Cubical.HITs.SetQuotients

  open import Multiset.ListQuotient.Base using () renaming (M to FMSet)
  open import Multiset.Coinductive.Trees as Trees
    using  (M-νM-FixpointEquiv)
    renaming (νM to LimList/Bisim)

  -- (LimList , Bisim) has a final FMSetoid coalgebra in setoids.
  Theorem5ExistsAna = anaMSEq
  Theorem5Uniqeness = anaMSUniq

  -- LimList/Bisim is a fixed point
  Theorem6 : FMSet LimList/Bisim ≃ LimList/Bisim
  Theorem6 = Trees.M-νM-FixpointEquiv

  -- Assuming choice, LimList/Bisim is a final coalgebra.
  module Theorem7 (θInv : ∀ A {B} (R : B → B → Type) → (A → B / R) → [ A ⇒ B ]/ R)
          (sectionθ : ∀ A {B} (R : B → B → Type) → section (θ A R) (θInv A R))
          where
    existsAna : {X : Type} (c : X → FMSet X) → X → LimList/Bisim
    existsAna = Trees.anaM θInv sectionθ

    uniqueness : {X : Type} → isSet X → (c : X → FMSet X) → {! !}
    uniqueness = Trees.anaMUniq θInv sectionθ
