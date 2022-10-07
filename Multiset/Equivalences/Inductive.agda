open import Multiset.Prelude

module Multiset.Equivalences.Inductive {X : Type} where

open import Multiset.Inductive as M
  using (M ; _⊕_)
open import Multiset.Ordering.Order as PList
  using (Perm ; stop ; perm)
  renaming (Mset to PList ; isSetMset to isSetPList)

open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Foundations.HLevels

open import Cubical.Data.List as List
  using (List ; _∷_ ; _++_ ; [])
open import Cubical.HITs.SetQuotients as SQ
  using ([_])
open import Cubical.HITs.FiniteMultiset as HeadPList
  using ()
  renaming (FMSet to HeadPList ; _++_ to _++ₚ_)


-- ============================================================= --
-- Equivalence of the HIT of a free commutative monoid on X and  --
-- lists of X modulo permutation.                                --
--                                                               --
-- Both types are commuative monoids, so we get maps back and    --
-- forth for free from the recursors.  To show they're mutual    --
-- inveres, show that they preserve the monoid multiplication.   --
-- ============================================================= --

Perm1ToMPath : ∀ {x y : X} (xs ys : List X)
  → M.fromList (xs ++ x ∷ y ∷ ys) ≡ M.fromList (xs ++ y ∷ x ∷ ys)
Perm1ToMPath [] ys = M.assoc _ _ _ ∙∙ cong (_⊕ M.fromList ys) (M.comm _ _) ∙∙ sym (M.assoc _ _ _)
Perm1ToMPath (x ∷ xs) ys = cong (x M.∷_) (Perm1ToMPath xs ys)

PermToMPath : ∀ {xs ys : List X}
  → Perm xs ys
  → M.fromList xs ≡ M.fromList ys
PermToMPath stop = refl
PermToMPath (perm {xs = xs} ps) = Perm1ToMPath xs _ ∙ PermToMPath ps

MToPList : M X → PList X
MToPList = M.rec isSetPList
  PList.emptyMset
  PList.singleton
  PList.concat
  PList.concat-unitˡ
  PList.concat-assoc
  PList.concat-comm

PListToM : PList X → M X
PListToM = PList.recMset M.isSetM M.fromList (λ as bs → PermToMPath)

PListToM-concat-to-⊕ : ∀ xs ys
  → PListToM (PList.concat xs ys) ≡ PListToM xs ⊕ PListToM ys
PListToM-concat-to-⊕ xs ys = PList.elimProp2Mset (λ xs ys → M.isSetM (PListToM (PList.concat xs ys)) (PListToM xs ⊕ PListToM ys)) goal xs ys where
  goal : (as bs : List X) → PListToM [ as ++ bs ] ≡ M.fromList as ⊕ M.fromList bs
  goal [] bs = sym (M.unit (M.fromList bs))
  goal (x ∷ as) bs =
    M.η x ⊕ M.fromList (as ++ bs)           ≡⟨ cong (M.η x ⊕_) (goal as bs) ⟩
    M.η x ⊕ (M.fromList as ⊕ M.fromList bs) ≡⟨ M.assoc (M.η x) (M.fromList as) (M.fromList bs) ⟩
    (M.η x ⊕ M.fromList as) ⊕ M.fromList bs ∎

open Iso

M-PList-Iso : Iso (M X) (PList X)
M-PList-Iso .fun = MToPList
M-PList-Iso .inv = PListToM
M-PList-Iso .leftInv = M.ind (λ xs → M.isSetM _ xs)
  refl
  (λ x → M.unit' (M.η x))
  pres-⊕ where
  pres-⊕ : ∀ {xs ys}
    → PListToM (MToPList xs) ≡ xs
    → PListToM (MToPList ys) ≡ ys
    → PListToM (MToPList (xs ⊕ ys)) ≡ xs ⊕ ys
  pres-⊕ {xs} {ys} indH-xs indH-ys =
    PListToM (MToPList (xs ⊕ ys)) ≡⟨⟩
    PListToM (PList.concat (MToPList xs) (MToPList ys)) ≡⟨ PListToM-concat-to-⊕ (MToPList xs) (MToPList ys) ⟩
    (PListToM (MToPList xs)) ⊕ (PListToM (MToPList ys)) ≡⟨ cong₂ _⊕_ indH-xs indH-ys ⟩
    xs ⊕ ys ∎
M-PList-Iso .rightInv = PList.elimPropMset (λ xs → isSetPList _ xs) pres-[] where
  pres-[] : (as : List X) → MToPList (PListToM [ as ]) ≡ [ as ]
  pres-[] [] = refl
  pres-[] (x ∷ as) =
    MToPList (x M.∷ PListToM [ as ])                     ≡⟨⟩
    PList.concat [ x ∷ [] ] (MToPList (PListToM [ as ])) ≡⟨ cong (PList.concat [ x ∷ [] ]) (pres-[] as) ⟩
    PList.concat [ x ∷ [] ] [ as ]                       ≡⟨⟩
    [ x ∷ as ] ∎

M≃PList : M X ≃ PList X
M≃PList = isoToEquiv M-PList-Iso

-- ============================================================= --
-- Equivalence of the HIT of a free commutative monoid on X and  --
-- lists of X modulo permutations at the head.                   --
--                                                               --
-- Same story as above, the only crucial bit is to prove that    --
-- the map HeadPList X → M X is a monoid homomorphism.           --
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
    HeadPListToM (x HeadPList.∷ (xs ++ₚ ys))    ≡⟨⟩
    x M.∷ HeadPListToM (xs ++ₚ ys)              ≡⟨ cong (x M.∷_) (indH ys) ⟩
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
    HeadPListToM (MToHeadPList xs ++ₚ MToHeadPList ys)              ≡⟨ isMonoidHomHeadPListToM (MToHeadPList xs) (MToHeadPList ys) ⟩
    HeadPListToM (MToHeadPList xs) ⊕ HeadPListToM (MToHeadPList ys) ≡⟨ cong₂ _⊕_ indH-xs indH-ys ⟩
    xs ⊕ ys ∎
M-HeadPList-Iso .rightInv = HeadPList.ElimProp.f (HeadPList.trunc _ _) refl goal where
  goal : ∀ x {xs}
    → MToHeadPList (HeadPListToM xs) ≡ xs
    → MToHeadPList (HeadPListToM (x HeadPList.∷ xs)) ≡ x HeadPList.∷ xs
  goal x {xs} indH-xs =
    HeadPList.[ x ] ++ₚ MToHeadPList (HeadPListToM xs) ≡⟨ cong (HeadPList.[ x ] ++ₚ_) indH-xs ⟩
    x HeadPList.∷ xs ∎

M≃HeadPList : M X ≃ HeadPList X
M≃HeadPList = isoToEquiv M-HeadPList-Iso
