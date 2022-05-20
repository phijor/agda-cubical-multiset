module Multiset.OverGroupoid.Properties where

open import Multiset.OverGroupoid.Base

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

import Cubical.Data.FinSet as FinSet
open import Cubical.Data.Nat as ℕ
  using (ℕ ; _+_)

private
  variable
    ℓ : Level
    X : Type ℓ

isGroupoidFMSet : isGroupoid X → isGroupoid (FMSet X)
isGroupoidFMSet h = isOfHLevelΣ 3 FinSet.isGroupoidFinSet λ _ → isOfHLevelΠ 3 (λ _ → h)

isOfHLevel₊₃FMSet : (n : ℕ) → (isOfHLevel (3 + n) X) → isOfHLevel (3 + n) (FMSet X)
isOfHLevel₊₃FMSet n h = isOfHLevelΣ (3 + n) lem λ _ → isOfHLevelΠ (3 + n) (λ _ → h) where
  lem : ∀ {ℓ} → isOfHLevel (3 + n) (FinSet.FinSet ℓ)
  lem = subst (λ k → isOfHLevel k (FinSet.FinSet _)) (ℕ.+-comm n 3) (isOfHLevelPlus n FinSet.isGroupoidFinSet)
