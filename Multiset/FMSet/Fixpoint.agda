{-# OPTIONS --safe #-}

module Multiset.FMSet.Fixpoint where

open import Multiset.Prelude
open import Multiset.Util.SetTruncation using (setTruncEquiv)
open import Multiset.Tote as Tote using (Tote ; FMSet≃∥Tote∥₂)
open import Multiset.FMSet as FMSet

open import Multiset.Bij
open import Multiset.Bag.Base as Bag using (Bag)
open import Multiset.Bag.Properties as Bag
  using (bagLimitEquiv ; BagLim ; Bag≃Tote)


open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

FMSetFixSetTruncTree : FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂
FMSetFixSetTruncTree =
  FMSet ∥ BagLim ∥₂ ≃⟨ isoToEquiv FMSet.STInvarianceIso ⟩
  FMSet BagLim      ≃⟨ FMSet≃∥Tote∥₂ ⟩
  ∥ Tote BagLim ∥₂  ≃⟨ setTruncEquiv (invEquiv step) ⟩
  ∥ BagLim ∥₂       ■ where

  step : BagLim ≃ Tote BagLim
  step =
    BagLim      ≃⟨ invEquiv bagLimitEquiv ⟩
    Bag BagLim  ≃⟨ Bag≃Tote ⟩
    Tote BagLim ■
