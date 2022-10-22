{-# OPTIONS --safe #-}

open import Multiset.Prelude

module Multiset.Equivalences.FCM-HeadPList {X : Type} where

open import Multiset.FCM as M
  using (M ; _⊕_)

open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Foundations.HLevels

open import Cubical.HITs.FiniteMultiset as HeadPList
  using (_++_)
  renaming (FMSet to HeadPList)

open Iso


-- ============================================================= --
-- Equivalence of the HIT of a free commutative monoid on X and  --
-- lists of X modulo permutations at the head.                   --
--                                                               --
-- The crucial bit here is to prove that HeadPList X → M X is a  --
-- monoid homomorphism.                                          --
-- ============================================================= --

MToHeadPList : M X → HeadPList X
MToHeadPList = M.rec HeadPList.trunc
  HeadPList.[] HeadPList.[_] HeadPList._++_
  (λ _ → refl) HeadPList.assoc-++ HeadPList.comm-++

HeadPListToM : HeadPList X → M X
HeadPListToM = HeadPList.Elim.f
  M.ε
  (λ x xs → x M.∷ xs)
  (λ x y xs → M.∷-swap x y xs)
  (λ _ → M.isSetM)

isMonoidHomHeadPListToM : ∀ xs ys
    → HeadPListToM (xs HeadPList.++ ys) ≡ HeadPListToM xs ⊕ HeadPListToM ys
isMonoidHomHeadPListToM = HeadPList.ElimProp.f (isPropΠ (λ ys → M.isSetM _ _))
  (λ ys → sym (M.unit (HeadPListToM ys)))
  λ x {xs} indH ys →
    HeadPListToM (x HeadPList.∷ (xs ++ ys))     ≡⟨⟩
    x M.∷ HeadPListToM (xs ++ ys)               ≡⟨ cong (x M.∷_) (indH ys) ⟩
    x M.∷ (HeadPListToM xs ⊕ HeadPListToM ys)   ≡⟨ M.assoc _ _ _ ⟩
    (M.η x ⊕ HeadPListToM xs) ⊕ HeadPListToM ys ≡⟨⟩
    HeadPListToM (x HeadPList.∷ xs) ⊕ HeadPListToM ys ∎

M-HeadPList-Iso : Iso (M X) (HeadPList X)
M-HeadPList-Iso .fun = MToHeadPList
M-HeadPList-Iso .inv = HeadPListToM
M-HeadPList-Iso .leftInv = M.ind (λ xs → M.isSetM _ xs) refl (λ x → M.unit' (M.η x)) goal where
  goal : ∀ {xs ys : M X} →
        HeadPListToM (MToHeadPList xs) ≡ xs →
        HeadPListToM (MToHeadPList ys) ≡ ys →
        HeadPListToM (MToHeadPList (xs ⊕ ys)) ≡ xs ⊕ ys
  goal {xs} {ys} indH-xs indH-ys =
    HeadPListToM (MToHeadPList (xs ⊕ ys))                           ≡⟨⟩
    HeadPListToM (MToHeadPList xs ++ MToHeadPList ys )              ≡⟨ isMonoidHomHeadPListToM (MToHeadPList xs) (MToHeadPList ys) ⟩
    HeadPListToM (MToHeadPList xs) ⊕ HeadPListToM (MToHeadPList ys) ≡⟨ cong₂ _⊕_ indH-xs indH-ys ⟩
    xs ⊕ ys ∎
M-HeadPList-Iso .rightInv = HeadPList.ElimProp.f (HeadPList.trunc _ _) refl goal where
  goal : ∀ x {xs}
    → MToHeadPList (HeadPListToM xs) ≡ xs
    → MToHeadPList (HeadPListToM (x HeadPList.∷ xs)) ≡ x HeadPList.∷ xs
  goal x {xs} indH-xs =
    HeadPList.[ x ] ++ MToHeadPList (HeadPListToM xs) ≡⟨ cong (HeadPList.[ x ] ++_) indH-xs ⟩
    x HeadPList.∷ xs ∎

M≃HeadPList : M X ≃ HeadPList X
M≃HeadPList = isoToEquiv M-HeadPList-Iso
