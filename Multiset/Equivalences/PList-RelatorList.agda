{-# OPTIONS --safe #-}

open import Multiset.Prelude

module Multiset.Equivalences.PList-RelatorList where

open import Multiset.ListQuotient.Base
  using (Relator; mapDRelator')
open import Multiset.Ordering.Order
  using (Perm; mapP)
open import Multiset.Ordering.PermEquiv
--  using (∥Perm∥₁≡Relator≡)

open import Cubical.Foundations.Everything
open import Cubical.Data.List as List hiding ([_])
open import Cubical.Data.Vec as Vec 
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ

open Iso

module _ {A : Type} where

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


module _ {A B : Type} (f : A → B) where

  map/∥Perm∥ : List A / ∥Perm∥₁ → List B / ∥Perm∥₁
  map/∥Perm∥ =
    rec squash/ (λ xs → [ List.map f xs ])
        (λ _ _ → PT.rec (squash/ _ _) (λ p → eq/ _ _ PT.∣ mapP f p ∣₁))

  map/Perm : List A / Perm → List B / Perm
  map/Perm = SQ.rec squash/ (λ xs → [ List.map f xs ]) λ as bs p → eq/ _ _ (mapP f p)

  map/Relator≡ : List A / Relator _≡_ → List B / Relator _≡_
  map/Relator≡ = 
    rec squash/ (λ xs → [ List.map f xs ])
        (λ _ _ r → eq/ _ _ (mapDRelator' (cong f) (r .fst) , mapDRelator' (cong f) (r .snd)))

  List/∥Perm∥→List/Relator≡-nat : (xs : List A / ∥Perm∥₁)
    → List/∥Perm∥→List/Relator≡ (map/∥Perm∥ xs) ≡ map/Relator≡ (List/∥Perm∥→List/Relator≡ xs)
  List/∥Perm∥→List/Relator≡-nat = SQ.elimProp (λ _ → squash/ _ _) λ _ → refl

  List/Perm→List/Relator≡-nat : (xs : List A / Perm)
    → List/Perm-List/Relator≡-Iso .fun (map/Perm xs) ≡ map/Relator≡ (List/Perm-List/Relator≡-Iso .fun xs)
  List/Perm→List/Relator≡-nat = SQ.elimProp (λ _ → squash/ _ _) λ _ → refl

  open import Multiset.ListQuotient.FMSetEquiv
  open import Multiset.FMSet.Properties as FMSet
  open import Cubical.Data.Nat
  open import Cubical.Data.FinData

  Vec→List-nat : ∀ {n} (xs : Vec A n) → Vec→List (Vec.map f xs) ≡ List.map f (Vec→List xs)
  Vec→List-nat [] = refl
  Vec→List-nat (x ∷ xs) = cong (λ y → f x List.∷ y) (Vec→List-nat xs)

  FinVec→Vec-nat : ∀ {n} xs → FinVec→Vec {n = n} (λ k → f (xs k)) ≡ Vec.map f (FinVec→Vec xs)
  FinVec→Vec-nat {zero} xs = refl
  FinVec→Vec-nat {suc n} xs = cong (λ x → f (xs zero) Vec.∷ x) (FinVec→Vec-nat {n} (xs ∘ suc))

  FMSet→List/Relator=-nat : ∀ xs
    → FMSet→List/Relator= (FMSet.map f xs) ≡ map/Relator≡ (FMSet→List/Relator= xs)
  FMSet→List/Relator=-nat =
    FMSet.elimProp (λ _ → squash/ _ _)
      (λ {n} xs → cong _/_.[_]
        (Vec→List (FinVec→Vec (λ k → f (xs (Fin→SumFin k))))          ≡⟨ cong Vec→List (FinVec→Vec-nat _) ⟩
        Vec→List (Vec.map f (FinVec→Vec (λ k → xs (Fin→SumFin k))))  ≡⟨ Vec→List-nat _ ⟩
        List.map f (Vec→List (FinVec→Vec (λ k → xs (Fin→SumFin k)))) ∎))
