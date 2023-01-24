{-# OPTIONS --safe #-}

module Multiset.Omniscience where

open import Multiset.Prelude

open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit.Base as Unit
open import Cubical.Data.Nat.Base as Nat
open import Cubical.Data.Bool.Base as Bool
open import Cubical.Data.Sum.Base as Sum

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    )
open import Cubical.Relation.Nullary using (Dec ; yes ; no)

LLPO : Type
LLPO = (a : ℕ → Bool)
  → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
  → ∥ (∀ n → isEvenT n → a n ≡ false) ⊎ (∀ n → isOddT n → a n ≡ false) ∥₁

isPropLLPO : isProp LLPO
isPropLLPO = isPropΠ2 (λ _ _ → PT.isPropPropTrunc)
