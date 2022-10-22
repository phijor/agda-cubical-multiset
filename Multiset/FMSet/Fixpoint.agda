{-# OPTIONS --safe #-}

module Multiset.FMSet.Fixpoint where

open import Multiset.Prelude
open import Multiset.Util.SetTruncation using (setTruncEquiv)
open import Multiset.OverGroupoid as OverGroupoid using (FMSet≃∥Tote∥₂) renaming (FMSet to Tote)
open import Multiset.FMSet as FMSet

open import Multiset.Bij
open import Multiset.Bag.Base as Bag
  using
    ( Bag
    ; Vect
    ; BagIsoΣ
    ; ⟨Bij→FinSet⟩≃Idx
    )
open import Multiset.Bag.Properties as Bag
  using (bagLimitEquiv ; BagLim)


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv)
open import Cubical.Data.FinSet using (FinSet)

abstract
  Vect≃⟨Bij→FinSet⟩ : (x : Bij) → (Vect BagLim x) ≃ (⟨ Bij→FinSet x ⟩ → BagLim)
  Vect≃⟨Bij→FinSet⟩ x = preCompEquiv (⟨Bij→FinSet⟩≃Idx x)

_ = Σ-cong-equiv

-- XXX: The below hypothesis follows from Σ-cong-equiv : A ≃ A' → (∀ x → B x ≃ B' x) → Σ A B ≃ Σ A' B'
-- applied to Bij≃FinSet and the above Vect≃⟨Bij→FinSet⟩.  But currently Agda tries to compute an
-- inverse(?) and loops/computes forever.  Feel free to try it yourself, I gave up after letting
-- Agda 2.6.2.2 attempt to type-check for an hour.
module _ (does-not-compute : (Σ[ x ∈ Bij ] (Vect BagLim x)) ≃ (Σ[ B ∈ FinSet ℓ-zero ] (⟨ B ⟩ → BagLim))) where

  FMSetFixSetTruncTree : (FMSet ∥ BagLim ∥₂) ≃ ∥ BagLim ∥₂
  FMSetFixSetTruncTree =
    (FMSet ∥ BagLim ∥₂) ≃⟨ isoToEquiv FMSet.STInvarianceIso ⟩
    (FMSet BagLim)      ≃⟨ FMSet≃∥Tote∥₂ ⟩
    (∥ Tote BagLim ∥₂)  ≃⟨ setTruncEquiv (invEquiv step) ⟩
    (∥ BagLim ∥₂)       ■ where

    step : BagLim ≃ (Tote BagLim)
    step =
      (BagLim)              ≃⟨ invEquiv bagLimitEquiv ⟩
      (Bag BagLim)          ≃⟨ isoToEquiv BagIsoΣ ⟩
      (Σ Bij (Vect BagLim)) ≃⟨ does-not-compute ⟩
      (Tote BagLim)         ■
