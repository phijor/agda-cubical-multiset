{-# OPTIONS --safe #-}

open import Multiset.Prelude

module Multiset.Equivalences.PList-RelatorList {A : Type} where

open import Multiset.ListQuotient.Base
  using (Relator)
open import Multiset.Ordering.Order
  using (Perm)
open import Multiset.Ordering.PermEquiv
  using (∥Perm∥₁≡Relator≡)

open import Cubical.Foundations.Everything
open import Cubical.Data.List as List
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ
  using (_/_ ; truncRelEquiv)

-- ============================================================= --
-- Equivalence lists of modulo permutation and lists modulo the  --
-- relational lifting of equality to lists.                      --
-- ============================================================= --

List/Perm≃List/Relator≡ : (List A / Perm) ≃ (List A / Relator _≡_)
List/Perm≃List/Relator≡ =
  List A / Perm                         ≃⟨ truncRelEquiv ⟩
  List A / (λ xs ys → ∥ Perm xs ys ∥₁)  ≃⟨ substEquiv (List A /_) (∥Perm∥₁≡Relator≡ {A = A}) ⟩
  List A / Relator _≡_ ■
