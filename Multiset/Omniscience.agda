{-# OPTIONS --safe #-}

module Multiset.Omniscience where

open import Multiset.Prelude

open import Cubical.Data.Nat.Base as Nat
open import Cubical.Data.Bool.Base as Bool
open import Cubical.Data.Sum.Base as Sum

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    )

LLPO : Type
LLPO = (a : ℕ → Bool)
  → isProp (Σ[ n ∈ ℕ ] a n ≡ true)
  → ∥ (∀ n → isEvenT n → a n ≡ false) ⊎ (∀ n → isOddT n → a n ≡ false) ∥₁
