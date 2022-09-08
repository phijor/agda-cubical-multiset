module Multiset.Inductive.Equiv where

open import Multiset.Prelude
open import Multiset.Inductive.Base as M

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Syntax.⟨⟩
open import Cubical.Functions.Logic as Logic
  renaming
    (¬_ to ¬ₚ_)
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    ; isPropPropTrunc
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; zero
    ; suc
    )
open import Cubical.Data.Unit as Unit
  using (Unit)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )

open import Cubical.Relation.Nullary.Base
  using
  (¬_)

open import Cubical.HITs.FiniteMultiset as FMSet

private
  variable
    ℓ : Level
    X : Type ℓ

toFMSet : M X → FMSet X
toFMSet = M.rec
  FMSet.trunc
  [] [_] (_++_)
  (λ _ → refl) assoc-++ comm-++

toM : FMSet X → M X
toM = FMSet.Rec.f isSetM ε M._∷_ ∷-swap

toM-hom : ∀ (xs ys : FMSet X) → toM (xs ++ ys) ≡ toM xs ⊕ toM ys
toM-hom xs ys = FMSet.ElimProp.f (isSetM _ _) nil* cons* xs where
  nil* : toM ([] ++ ys) ≡ toM [] ⊕ toM ys
  nil* = sym (unit (toM ys))

  cons* : ∀ z {zs}
    → toM (zs ++ ys) ≡ toM zs ⊕ toM ys
    → toM ((z FMSet.∷ zs) ++ ys) ≡ toM (z FMSet.∷ zs) ⊕ toM ys
  cons* z {zs} indH =
    toM ((z FMSet.∷ zs) ++ ys)  ≡⟨⟩
    toM (z FMSet.∷ (zs ++ ys))  ≡⟨⟩
    z M.∷ toM (zs ++ ys)        ≡⟨ cong (z M.∷_) indH ⟩
    z M.∷ (toM zs ⊕ toM ys)     ≡⟨⟩
    η z ⊕ (toM zs ⊕ toM ys)     ≡⟨ M.assoc _ _ _ ⟩
    (η z ⊕ toM zs) ⊕ toM ys     ≡⟨⟩
    toM (z FMSet.∷ zs) ⊕ toM ys ∎

open Iso
M-FMSet-Iso : Iso (M X) (FMSet X)
M-FMSet-Iso .fun = toFMSet
M-FMSet-Iso .inv = toM
M-FMSet-Iso .leftInv = M.ind (λ _ → isSetM _ _) empty* singl* union*
  where

  empty* : toM (toFMSet ε) ≡ ε
  empty* = refl

  singl* : ∀ x → toM (toFMSet (η x)) ≡ η x
  singl* x = unit' (η x)

  union* : ∀ {xs ys : M X}
    → toM (toFMSet xs) ≡ xs
    → toM (toFMSet ys) ≡ ys
    → toM (toFMSet (xs ⊕ ys)) ≡ xs ⊕ ys
  union* {xs = xs} {ys = ys} linv-xs linv-ys =
    toM (toFMSet (xs ⊕ ys))             ≡⟨⟩
    toM (toFMSet xs ++ toFMSet ys)      ≡⟨ toM-hom (toFMSet xs) (toFMSet ys) ⟩
    toM (toFMSet xs) ⊕ toM (toFMSet ys) ≡⟨ cong₂ _⊕_ linv-xs linv-ys ⟩
    xs ⊕ ys ∎
M-FMSet-Iso .rightInv = FMSet.ElimProp.f (FMSet.trunc _ _) nil* cons*
  where

  nil* : toFMSet (toM []) ≡ []
  nil* = refl

  cons* : ∀ (x : X) {xs : FMSet X} →
    toFMSet (toM xs) ≡ xs →
    toFMSet (toM (x FMSet.∷ xs)) ≡ x FMSet.∷ xs
  cons* x {xs} indH =
    toFMSet (toM (x FMSet.∷ xs))      ≡⟨⟩
    toFMSet (η x) ++ toFMSet (toM xs) ≡⟨ cong (toFMSet (η x) ++_) indH ⟩
    toFMSet (η x) ++ xs               ≡⟨⟩
    [ x ] ++ xs                       ≡⟨⟩
    (x FMSet.∷ xs) ∎
