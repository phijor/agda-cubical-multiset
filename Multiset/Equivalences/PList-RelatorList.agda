{-# OPTIONS --safe #-}

open import Multiset.Prelude

module Multiset.Equivalences.PList-RelatorList {A : Type} where

open import Multiset.ListQuotient.Base
  using (Relator)
open import Multiset.Ordering.Order
  using (Perm)
open import Multiset.Ordering.PermEquiv
--  using (∥Perm∥₁≡Relator≡)

open import Cubical.Foundations.Everything
open import Cubical.Data.List as List hiding ([_])
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ
--  using (_/_ ; truncRelEquiv)

-- ============================================================= --
-- Equivalence lists of modulo permutation and lists modulo the  --
-- relational lifting of equality to lists.                      --
-- ============================================================= --

List/∥Perm∥≃List/Relator≡ : (List A / (λ xs ys → ∥ Perm xs ys ∥₁)) ≃ (List A / Relator _≡_)
List/∥Perm∥≃List/Relator≡ = isoToEquiv
  (iso (SQ.rec squash/ [_] λ _ _ → PT.rec (squash/ _ _) (eq/ _ _ ∘ Perm→Relator=) )
       (SQ.rec squash/ [_] λ _ _ → eq/ _ _ ∘ Relator=→∥Perm∥₁)
       (SQ.elimProp (λ _ → squash/ _ _) λ _ → refl)
       (SQ.elimProp (λ _ → squash/ _ _) λ _ → refl))

List/Perm≃List/Relator≡ : (List A / Perm) ≃ (List A / Relator _≡_)
List/Perm≃List/Relator≡ =
  List A / Perm                         ≃⟨ truncRelEquiv ⟩
  List A / (λ xs ys → ∥ Perm xs ys ∥₁)  ≃⟨ List/∥Perm∥≃List/Relator≡ ⟩
  --substEquiv (List A /_) (∥Perm∥₁≡Relator≡ {A = A}) ⟩
  List A / Relator _≡_ ■
