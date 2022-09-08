module Multiset.VectQuot.Base where

open import Multiset.Prelude

open import Cubical.Data.Nat as Nat
open import Cubical.Data.Vec as Vec

private
  variable
    ℓ : Level
    A : Type ℓ

data Perm {ℓ} {A : Type ℓ} : {n : ℕ} (v w : Vec A n) → Type ℓ where
  nil~ : Perm [] []
  -- cons~ : ∀ {x y} {xs ys} → Perm xs ys → 
