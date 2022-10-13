{-# OPTIONS --safe #-}

module Multiset.Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.SetTruncation as ST

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

open Iso

module HIT where
  open import Cubical.HITs.FiniteMultiset as FMSet
    using
      ( FMSet
      ; _∷_
      ; []
      ; [_]
      )

  ∣_∣₂∷_ :  X → FMSet ∥ X ∥₂ → FMSet ∥ X ∥₂
  ∣ x ∣₂∷ xs = ∣ x ∣₂ ∷ xs

  ∣∣₂∷-comm : (x y : X) → (xs : FMSet ∥ X ∥₂) → ∣ x ∣₂ ∷ ∣ y ∣₂ ∷ xs ≡ ∣ y ∣₂ ∷ ∣ x ∣₂ ∷ xs
  ∣∣₂∷-comm x y xs = FMSet.comm ∣ x ∣₂ ∣ y ∣₂ xs

  FMSet→FMSet∥∥₂ : FMSet X → FMSet ∥ X ∥₂
  FMSet→FMSet∥∥₂ = FMSet.Rec.f FMSet.trunc [] ∣_∣₂∷_ ∣∣₂∷-comm

  _∷*_ : ∥ X ∥₂ → FMSet X → FMSet X
  _∷*_ = ST.rec (isSetΠ (λ _ → FMSet.trunc)) _∷_

  ∷*-comm : (x y : ∥ X ∥₂) → (xs : FMSet X) → x ∷* (y ∷* xs) ≡ y ∷* (x ∷* xs)
  ∷*-comm ∣x∣ ∣y∣ xs = ST.elim2 {C = λ ∣x∣ ∣y∣ → ∣x∣ ∷* (∣y∣ ∷* xs) ≡ ∣y∣ ∷* (∣x∣ ∷* xs)}
    (λ _ _ → isProp→isSet (FMSet.trunc _ _))
    (λ x y → FMSet.comm x y xs) ∣x∣ ∣y∣

  FMSet∥∥₂→FMSet : FMSet ∥ X ∥₂ → FMSet X
  FMSet∥∥₂→FMSet = FMSet.Rec.f FMSet.trunc [] _∷*_ ∷*-comm

  FMSet≅FMSet∥∥₂ : Iso (FMSet X) (FMSet ∥ X ∥₂)
  FMSet≅FMSet∥∥₂ .fun = FMSet→FMSet∥∥₂
  FMSet≅FMSet∥∥₂ .inv = FMSet∥∥₂→FMSet
  FMSet≅FMSet∥∥₂ {X = X} .rightInv =
    FMSet.ElimProp.f (FMSet.trunc _ _) refl lemma where
      lemma : (∣x∣ : ∥ X ∥₂)
        → {xs : FMSet ∥ X ∥₂}
        → FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet xs) ≡ xs
        → FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet (∣x∣ ∷ xs)) ≡ ∣x∣ ∷ xs
      lemma = ST.elim
        {B = λ ∣x∣ → ∀ {xs} → (FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet xs) ≡ xs) → FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet (∣x∣ ∷ xs)) ≡ ∣x∣ ∷ xs}
        (λ ∣x∣ → isSetImplicitΠ λ xs → isSetΠ λ p → isProp→isSet (FMSet.trunc _ _))
        (λ x → cong ∣ x ∣₂∷_)
  FMSet≅FMSet∥∥₂ .leftInv = FMSet.ElimProp.f (FMSet.trunc _ _) (refl {x = []}) λ x → cong (x ∷_)

  FMSet≃FMSet∥∥₂ : FMSet X ≃ FMSet ∥ X ∥₂
  FMSet≃FMSet∥∥₂ = isoToEquiv FMSet≅FMSet∥∥₂
