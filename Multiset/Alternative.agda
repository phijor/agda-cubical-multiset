module Multiset.Alternative where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.HITs.PropositionalTruncation

record Finite : Type₁ where
   field
     N : Type
     size : ℕ
     equiv : ∥ N ≃ Fin size ∥ -- ∥-∥ says "forget the information inside"

open Finite

M' : Type → Type₁
M' X = Σ Finite λ B → B .N → X

-- Problems:

-- -- Type₁, we cannot do ω-chains

-- -- It is not a set:
-- -- -- Given (X , n , p), (Y , m , q) and eq, eq' : (X , n , p) ≡ (Y , m , q),
-- -- -- try to prove eq = eq'. Not possible since not all n-permutations are equal

  -- isSet-Finite : isSet Finite
  -- isSet-Finite = {!   !}

  -- isSet-M' : (X : Type) → isSet (M' X)
  -- isSet-M' X = isSetΣ isSet-Finite {!   !}
  -- isSet-M' X M N = λ eq eq' → {!   !}

-- -- There is no way of fixing this, in the sense that you cannot add
-- -- finite number of coherences to get out a set

-- -- Check also: Buchholtz'21
-- -- https://www2.mathematik.tu-darmstadt.de/~buchholtz/pairs.pdf
