-- Define the finite multiset functor M (HITs)
-- Define the ω-chain 1 <- M 1 <- M (M 1) <- ...
-- Construct the limit L
-- Prove that L is the final coalgebra of M
-- Look at other ways of constructing the final coalgebra (coinductive types)

module Multiset.Multiset where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

open import Multiset.Base renaming (map to mapM)
open import Multiset.Algebra using
  ( rec
  ; M-M-alg
  )
open import Multiset.Limits

iterM : ℕ → Type → Type
iterM zero X = X
iterM (suc n) X = M (iterM n X)

iter! : (n : ℕ) → iterM (suc n) Unit → iterM n Unit
iter! zero x = tt
iter! (suc n) x = mapM (iter! n) x

record ωTree : Type where
  field
    branch : (n : ℕ) → iterM n Unit
    natural : (n : ℕ) → iter! n (branch (suc n)) ≡ branch n

!-ωChain : ωChain
!-ωChain = record
  { ob = λ n → iterM n Unit
  ; ∂ = iter!
  }

open module MCone = Multiset.Limits.ωCone !-ωChain

Lim : ωCone
Lim = record
  { Apex = ωTree
  ; leg = λ n vr → vr .branch n
  ; cond = λ n vr → vr .natural n
  } where open ωTree

Lim-map : (V : ωCone) → V .Apex → ωTree
Lim-map V v = record
  { branch = λ n → V .leg n v
  ; natural = λ n → V .cond n v
  }

Lim-up-∃ : (V : ωCone) → ωConeMap V Lim
Lim-up-∃ V = record
  { map = Lim-map V
  ; commutes = λ n v → refl
  }

Lim-up-! : (V : ωCone) (f : ωConeMap V Lim)
  → Lim-up-∃ V ≡ f
Lim-up-! V f i = record
  { map = λ v → {!   !}
  ; commutes = {!   !}
  }

Lim-is-Limit : is-Limit Lim
Lim-is-Limit V = (Lim-up-∃ V) , (Lim-up-! V)
