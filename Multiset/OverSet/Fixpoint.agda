{-# OPTIONS --allow-unsolved-metas #-}

module Multiset.OverSet.Fixpoint where

open import Multiset.Prelude
open import Multiset.Util.SetTruncation using (setTruncEquiv)
open import Multiset.OverGroupoid as OverGroupoid using (FMSet≃∥Tote∥₂) renaming (FMSet to Tote)
open import Multiset.OverSet as OverSet

open import Multiset.Bij
open import Multiset.OverBij.Base as OverBij
  using
    ( Bag
    ; Vect
    ; BagIsoΣ
    ; ⟨Bij→FinSet⟩≃Idx
    )
open import Multiset.OverBij.Properties as OverBij
  using (bagLimitIso)
  renaming (ωTree to BagLim)


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv)

FMSetFixSetTruncTree : (FMSet ∥ BagLim ∥₂) ≃ ∥ BagLim ∥₂
FMSetFixSetTruncTree =
  (FMSet ∥ BagLim ∥₂) ≃⟨ isoToEquiv OverSet.STInvarianceIso ⟩
  (FMSet BagLim)      ≃⟨ FMSet≃∥Tote∥₂ ⟩
  (∥ Tote BagLim ∥₂)  ≃⟨ setTruncEquiv (invEquiv step) ⟩
  (∥ BagLim ∥₂)       ■ where

  abstract
    Vect≃⟨Bij→FinSet⟩ : (x : Bij) → (Vect BagLim x) ≃ (⟨ Bij→FinSet x ⟩ → BagLim)
    Vect≃⟨Bij→FinSet⟩ x = preCompEquiv (⟨Bij→FinSet⟩≃Idx x)

  step : BagLim ≃ (Tote BagLim)
  step =
    (BagLim)               ≃⟨ isoToEquiv bagLimitIso ⟩
    (Bag BagLim)           ≃⟨ isoToEquiv BagIsoΣ ⟩
    -- TODO: Use a version of Σ-cong-equiv that does not compute the inverse of
    -- Bij≃FinSet using isoToEquiv.
    (Σ Bij (Vect BagLim))  ≃⟨ {! Σ-cong-equiv Bij≃FinSet Vect≃⟨Bij→FinSet⟩ !} ⟩
    (Tote BagLim)            ■
