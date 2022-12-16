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

open Iso

∥Perm∥₁ : (xs ys : List A) → Type
∥Perm∥₁ xs ys = ∥ Perm xs ys ∥₁

-- ============================================================= --
-- Equivalence lists of modulo permutation and lists modulo the  --
-- relational lifting of equality to lists.                      --
-- ============================================================= --

List/∥Perm∥→List/Relator≡ : List A / ∥Perm∥₁ → List A / Relator _≡_
List/∥Perm∥→List/Relator≡ = SQ.rec squash/ [_] λ _ _ → PT.rec (squash/ _ _) (eq/ _ _ ∘ Perm→Relator=)

List/Relator≡→List/∥Perm∥ : List A / Relator _≡_ → List A / ∥Perm∥₁
List/Relator≡→List/∥Perm∥ = SQ.rec squash/ [_] λ _ _ → eq/ _ _ ∘ Relator=→∥Perm∥₁

abstract
  List/∥Perm∥-List/Relator≡-rightInv : section List/∥Perm∥→List/Relator≡ List/Relator≡→List/∥Perm∥
  List/∥Perm∥-List/Relator≡-rightInv = SQ.elimProp (λ _ → squash/ _ _) λ _ → refl

  List/∥Perm∥-List/Relator≡-leftInv : retract List/∥Perm∥→List/Relator≡ List/Relator≡→List/∥Perm∥
  List/∥Perm∥-List/Relator≡-leftInv = SQ.elimProp (λ _ → squash/ _ _) λ _ → refl

List/∥Perm∥-List/Relator≡-Iso : Iso (List A / ∥Perm∥₁) (List A / Relator _≡_)
List/∥Perm∥-List/Relator≡-Iso .fun = List/∥Perm∥→List/Relator≡
List/∥Perm∥-List/Relator≡-Iso .inv = List/Relator≡→List/∥Perm∥
List/∥Perm∥-List/Relator≡-Iso .rightInv = List/∥Perm∥-List/Relator≡-rightInv
List/∥Perm∥-List/Relator≡-Iso .leftInv = List/∥Perm∥-List/Relator≡-leftInv

List/∥Perm∥≃List/Relator≡ : (List A / ∥Perm∥₁) ≃ (List A / Relator _≡_)
List/∥Perm∥≃List/Relator≡ = isoToEquiv List/∥Perm∥-List/Relator≡-Iso

List/Perm-List/Relator≡-Iso : Iso (List A / Perm) (List A / Relator _≡_)
List/Perm-List/Relator≡-Iso =
  List A / Perm           Iso⟨ truncRelIso ⟩
  List A / ∥Perm∥₁        Iso⟨ List/∥Perm∥-List/Relator≡-Iso ⟩
  (List A / Relator _≡_) ∎Iso

List/Perm≃List/Relator≡ : (List A / Perm) ≃ (List A / Relator _≡_)
List/Perm≃List/Relator≡ = isoToEquiv List/Perm-List/Relator≡-Iso
