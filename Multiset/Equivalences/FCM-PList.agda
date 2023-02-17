{-# OPTIONS --safe #-}

open import Multiset.Prelude

module Multiset.Equivalences.FCM-PList where

open import Multiset.FCM as M
  using (M ; _⊕_) renaming (map to mapM)
open import Multiset.Ordering.Order as PList
  using (Perm ; stop ; perm)
  renaming (Mset to PList ; isSetMset to isSetPList; mapMset to mapPList)

open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; isoToEquiv)
open import Cubical.Foundations.HLevels

open import Cubical.Data.List as List using (List ; _∷_ ; _++_ ; [])
open import Cubical.HITs.SetQuotients as SQ using ([_])

-- ============================================================= --
-- Equivalence of the HIT of a free commutative monoid on X and  --
-- lists of X modulo permutation.                                --
--                                                               --
-- Both types are commuative monoids, so we get maps back and    --
-- forth for free from the recursors.  To show they're mutual    --
-- inveres, show that they preserve the monoid multiplication.   --
-- ============================================================= --

module _ {X : Type} where

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

PListToM-nat' : {X Y : Type} (f : X → Y) (xs : List X)
  → PListToM [ List.map f xs ] ≡ mapM f (PListToM [ xs ])
PListToM-nat' f [] = refl
PListToM-nat' f (x ∷ xs) = cong (λ a → M.η (f x) ⊕ a) (PListToM-nat' f xs)

PListToM-nat : {X Y : Type} (f : X → Y) (xs : PList X)
  → PListToM (mapPList f xs) ≡ mapM f (PListToM xs)
PListToM-nat f = PList.elimPropMset (λ _ → M.isSetM _ _) (PListToM-nat' f)
