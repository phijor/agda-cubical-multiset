{-# OPTIONS --safe #-}

module Multiset.Ordering.FMSetOrder where


open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Vec hiding (length)
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin renaming (Fin to SumFin)
  hiding (discreteFin; Fin→SumFin; SumFin→Fin;
          SumFin→Fin→SumFin; Fin→SumFin→Fin; SumFin≃Fin)
open import Cubical.Data.FinData renaming (znots to znotsF; snotz to snotzF)
  hiding (eq; isSetFin)
open import Cubical.Data.Nat
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Binary
open BinaryRelation
open isEquivRel
open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum
open import Multiset.ListQuotient.Base hiding (M)
open import Multiset.ListQuotient.FMSetEquiv
open import Multiset.FMSet.Base
open import Multiset.FMSet.Properties hiding ([]; [_]; _∷_)
  renaming (map to mapFMSet)
open import Multiset.Ordering.Order
open import Multiset.Ordering.PermEquiv
open import Multiset.Equivalences.PList-RelatorList

module SortingFMSet {A : Type} (setA : isSet A)
  (R : A → A → Type)
  (linR : isLinOrder R) where

  open isLinOrder linR
  open Sorting setA R linR

  lengthInsert : (x : A) (xs : List A)
    → length (insert x xs) ≡ suc (length xs)
  lengthInsert x [] = refl
  lengthInsert x (y ∷ xs) =
    elimTotR R
             (λ z → length (casesTotR R (x ∷ y ∷ xs) (y ∷ insert x xs) (x ∷ y ∷ xs) z)
                      ≡ suc (suc (length xs)))
             (λ _ → refl)
             (λ _ → cong suc (lengthInsert x xs))
             (λ _ → refl)
             (totR x y)

  lengthSort : (xs acc : List A)
    → length (sort xs acc) ≡ length xs + length acc
  lengthSort [] acc = refl
  lengthSort (x ∷ xs) acc =
    lengthSort xs (insert x acc)
    ∙ cong′ (length xs +_) (lengthInsert x acc)
    ∙ +-suc _ _

  lengthSortPVect : (n : ℕ) (x : PVect A n)
    → length (sortMset (invEq List/Perm≃List/Relator≡ (FMSet→List/Relator= (n , x)))) ≡ n
  lengthSortPVect n =
    SQ.elimProp (λ _ → isSetℕ _ _)
             (λ v → lengthSort (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))) []
                     ∙ +-zero _
                     ∙ lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin)))

  sortFMSet : FMSet A → Σ ℕ λ n → SumFin n → A
  sortFMSet (n , x) =
    _ ,
    Vec→FinVec (List→Vec (sortMset (invEq List/Perm≃List/Relator≡ (FMSet→List/Relator= (n , x))))) ∘ SumFin→Fin

  sortFMSet-section : (x : FMSet A) → (_ , [ sortFMSet x .snd ]) ≡ x
  sortFMSet-section x =
    (_ , [ sortFMSet x .snd ])
      ≡⟨ refl ⟩
    List/Relator=→FMSet (equivFun List/Perm≃List/Relator≡ [ sortMset (invEq List/Perm≃List/Relator≡ (FMSet→List/Relator= x)) ])
      ≡⟨ (λ i → List/Relator=→FMSet (equivFun List/Perm≃List/Relator≡ (sortMset-section (invEq List/Perm≃List/Relator≡ (FMSet→List/Relator= x)) i))) ⟩
    List/Relator=→FMSet (equivFun List/Perm≃List/Relator≡ (invEq List/Perm≃List/Relator≡ (FMSet→List/Relator= x)))
      ≡⟨ (λ i → List/Relator=→FMSet (Iso.rightInv (equivToIso List/Perm≃List/Relator≡) (FMSet→List/Relator= x) i)) ⟩
    List/Relator=→FMSet (FMSet→List/Relator= x)
      ≡⟨ List/Relator=→FMSet→List/Relator= (x .fst) (x .snd) ⟩
    x
      ∎

  sortPVect : ∀ n → PVect A n → SumFin n → A
  sortPVect n x = subst (λ m → SumFin m → A) (lengthSortPVect n x) (sortFMSet (n , x) .snd)

-- Proposition 1
  sortPVect-section : ∀ n (x : PVect A n) → [ sortPVect n x ] ≡ x
  sortPVect-section n x =
    lem (lengthSortPVect n x) (sortFMSet (n , x) .snd)
    ∙ (subst (PVect A) (lengthSortPVect n x) [ sortFMSet (n , x) .snd ]
        ≡⟨ (λ i → subst (PVect A) (isSetℕ _ _ (lengthSortPVect n x) (cong size (sortFMSet-section (n , x))) i) [ sortFMSet (n , x) .snd ]) ⟩
        subst (PVect A) (cong size (sortFMSet-section (n , x))) [ sortFMSet (n , x) .snd ] ∎)
    ∙ fromPathP (cong snd (sortFMSet-section (n , x)))
    where
      lem : ∀{n m} (eq : n ≡ m) v
        → Path (PVect A m) [ subst (λ n → SumFin n → A) eq v ] (subst (PVect A) eq [ v ])
      lem = J (λ m eq → ∀ v → [ subst (λ n → SumFin n → A) eq v ] ≡ subst (PVect A) eq [ v ])
              λ v → cong′ [_] (substRefl {B = (λ n → SumFin n → A)} v)
                     ∙ sym (substRefl {B = PVect A} [ v ])

  TriplesPath : ∀{n m} {v w : SumFin n → A} {v' w' : SumFin m → A}
    → (eq : n ≡ m)
    → PathP (λ i → SumFin (eq i) → A) v v'
    → PathP (λ i → SumFin (eq i) → A) w w'
    → Path (Σ[ n ∈ ℕ ] (SumFin n → A) × (SumFin n → A)) (n , v , w) (m , v' , w')
  TriplesPath eqn eqv eqw = ΣPathP (eqn , λ i → eqv i , eqw i)

  SymmetricActionΣPath : {x y : Σ[ n ∈ ℕ ] (SumFin n → A) × (SumFin n → A)}
    → x ≡ y
    → SymmetricActionΣ (x .fst) (x .snd .fst) (x .snd .snd)
    → SymmetricActionΣ (y .fst) (y .snd .fst) (y .snd .snd)
  SymmetricActionΣPath eq p =
    J (λ y eq → SymmetricActionΣ (y .fst) (y .snd .fst) (y .snd .snd)) p eq

  substFinVec : ∀ {ℓ} {X : Type ℓ} {n m} (v : Fin n → X) (eq : n ≡ m)
    → subst (λ n → SumFin n → X) eq (v ∘ SumFin→Fin)
            ≡ subst (λ n → Fin n → X) eq v ∘ SumFin→Fin
  substFinVec {X = X} v =
    J (λ m eq → subst (λ n → SumFin n → X) eq (v ∘ SumFin→Fin)
                      ≡ subst (λ n → Fin n → X) eq v ∘ SumFin→Fin)
      (substRefl {B = λ n → SumFin n → X} (v ∘ SumFin→Fin)
      ∙ sym (cong′ (λ x → x ∘ SumFin→Fin) (substRefl {B = λ n → Fin n → X} v)))

  substVec→FinVec : ∀ {ℓ} {X : Type ℓ} {n m} (xs : Vec X n) (eq : n ≡ m)
    → subst (λ n → Fin n → X) eq (Vec→FinVec xs)
            ≡ Vec→FinVec (subst (Vec X) eq xs)
  substVec→FinVec {X = X} xs =
    J (λ m eq → subst (λ n → Fin n → X) eq (Vec→FinVec xs)
                      ≡ Vec→FinVec (subst (Vec X) eq xs))
      (substRefl {B = λ n → Fin n → X} (Vec→FinVec xs)
      ∙ sym (cong′ Vec→FinVec (substRefl {B = Vec X} xs)))


  canonicalS' : ∀ n (v w : SumFin n → A)
    → (eq : length (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))) ≡ length (Vec→List (FinVec→Vec (w ∘ Fin→SumFin))))
    → SymmetricActionΣ (length (Vec→List (FinVec→Vec (w ∘ Fin→SumFin))))
                        (Vec→FinVec (subst (Vec A) eq (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))) ∘ SumFin→Fin)
                        (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (w ∘ Fin→SumFin)))) ∘ SumFin→Fin)
    → SymmetricActionΣ n v w
  canonicalS' n v w eq =
    SymmetricActionΣPath (TriplesPath
      (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin)))
       (toPathP
          (subst (λ x → SumFin x → A) (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (Vec→FinVec (subst (Vec A) eq (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))) ∘ SumFin→Fin)
             ≡⟨ substFinVec (Vec→FinVec (subst (Vec A) eq (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))))
                             (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) ⟩
           subst (λ x → Fin x → A) (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (Vec→FinVec (subst (Vec A) eq (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))))) ∘ SumFin→Fin
             ≡⟨ (λ i → subst (λ x → Fin x → A)
                             (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin)))
                             (substVec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))) eq (~ i))
                         ∘ SumFin→Fin) ⟩
           subst (λ x → Fin x → A)
            (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin)))
            (subst (λ x → Fin x → A) eq (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))))) ∘ SumFin→Fin
             ≡⟨ cong (_∘ SumFin→Fin) (sym (substComposite (λ x → Fin x → A) eq (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))))) ⟩
           subst (λ x → Fin x → A) (eq ∙ lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))) ∘ SumFin→Fin
             ≡⟨ (λ i → subst (λ x → Fin x → A)
                              (isSetℕ _ _ (eq ∙ lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin))) i)
                              (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))))
                         ∘ SumFin→Fin) ⟩
           subst (λ x → Fin x → A) (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin))) (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))) ∘ SumFin→Fin
             ≡⟨ (λ i → substVec→FinVec (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin)))) (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin))) i ∘ SumFin→Fin ) ⟩
           Vec→FinVec (subst (Vec A) (lengthVec→List (FinVec→Vec (v ∘ Fin→SumFin))) (List→Vec (Vec→List (FinVec→Vec (v ∘ Fin→SumFin))))) ∘ SumFin→Fin
             ≡⟨ (λ i → Vec→FinVec (List→Vec→List (FinVec→Vec (v ∘ Fin→SumFin)) i) ∘ SumFin→Fin) ⟩
           Vec→FinVec (FinVec→Vec (v ∘ Fin→SumFin)) ∘ SumFin→Fin
             ≡⟨ (λ i → FinVec→Vec→FinVec (v ∘ Fin→SumFin) i ∘ SumFin→Fin) ⟩
           v ∘ Fin→SumFin ∘ SumFin→Fin
             ≡⟨ (λ i k → v (SumFin→Fin→SumFin k i)) ⟩
           v
             ∎))
       (toPathP
          (subst (λ x → SumFin x → A) (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (w ∘ Fin→SumFin)))) ∘ SumFin→Fin)
             ≡⟨ substFinVec (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (w ∘ Fin→SumFin)))))
                            (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) ⟩
           subst (λ x → Fin x → A) (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (Vec→FinVec (List→Vec (Vec→List (FinVec→Vec (w ∘ Fin→SumFin))))) ∘ SumFin→Fin
             ≡⟨ ((λ i → substVec→FinVec (List→Vec (Vec→List (FinVec→Vec (w ∘ Fin→SumFin)))) (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) i ∘ SumFin→Fin )) ⟩
           Vec→FinVec (subst (Vec A) (lengthVec→List (FinVec→Vec (w ∘ Fin→SumFin))) (List→Vec (Vec→List (FinVec→Vec (w ∘ Fin→SumFin))))) ∘ SumFin→Fin
             ≡⟨ (λ i → Vec→FinVec (List→Vec→List (FinVec→Vec (w ∘ Fin→SumFin)) i) ∘ SumFin→Fin) ⟩
           Vec→FinVec (FinVec→Vec (w ∘ Fin→SumFin)) ∘ SumFin→Fin
             ≡⟨ (λ i → FinVec→Vec→FinVec (w ∘ Fin→SumFin) i ∘ SumFin→Fin) ⟩
           w ∘ Fin→SumFin ∘ SumFin→Fin
             ≡⟨ (λ i k → w (SumFin→Fin→SumFin k i)) ⟩
           w
             ∎)))

-- Proposition 2
  canonicalS : ∀ n (v w : SumFin n → A)
    → SymmetricAction n v w
    → SymmetricActionΣ n v w
  canonicalS n v w r =
    rec→Set (isSetSymmetricActionΣ setA)
             (λ p → sa (canonicalP xs ys p))
             (λ p q i → canonicalS' n v w (lengthRelatorΣ (Perm→RelatorΣ= (canonicalP-const xs ys p q i))) (sa' (canonicalP-const xs ys p q i)))
             (Relator=→∥Perm∥₁ (SymAct→Relator= _ (w ∘ Fin→SumFin) (SymmetricAction→SymAct v w r)))
    where
      xs = Vec→List (FinVec→Vec (v ∘ Fin→SumFin))
      ys = Vec→List (FinVec→Vec (w ∘ Fin→SumFin))
      w' = Vec→FinVec (List→Vec ys)

      sa' : (p : Perm xs ys) → SymmetricActionΣ (length ys) _ (w' ∘ SumFin→Fin)
      sa' p = SymActΣ→SymmetricActionΣ _ w' (RelatorΣ=→SymActΣ xs ys (Perm→RelatorΣ= p))

      sa : Perm xs ys → SymmetricActionΣ n v w
      sa p = canonicalS' n v w (lengthRelatorΣ (Perm→RelatorΣ= p)) (sa' p)

      abstract
        isSet→Path : ∀ x → isSet (PathP (λ i → ua x i → A) v w)
        isSet→Path x = isOfHLevelPathP 2 (isSet→ setA) v w
