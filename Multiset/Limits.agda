module Multiset.Limits where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat

record ωChain : Type₁ where
  field
    ob : ℕ → Type
    ∂ : (n : ℕ) → ob (suc n) → ob n

module ωCone (F : ωChain) where

  record ωCone : Type₁ where
    open ωChain
    field
      Apex : Type
      leg : (n : ℕ) → Apex → F .ob n
      cond : (n : ℕ) (v : Apex) → F .∂ n (leg (suc n) v) ≡ leg n v

  record ωConeMap (V W : ωCone) : Type where
    open ωCone
    field
      map : V .Apex → W .Apex
      commutes : (n : ℕ) → (v : V .Apex) → W .leg n (map v) ≡ V .leg n v

  is-Limit : (ωCone) → Type₁
  is-Limit L = (V : ωCone) → isContr (ωConeMap V L)

  open ωCone public
  open ωConeMap public
