module Multiset.Analytic.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base
open import Cubical.Algebra.Group.Base

open import Multiset.GroupAction.Base

private
  variable
    ℓ ℓG ℓσ : Level

record SignatureStr (ℓG ℓS : Level) (Op : Type ℓ) : Type (ℓ-max (ℓ-max ℓ (ℓ-suc ℓG)) (ℓ-suc ℓS)) where

  constructor signaturestr

  field
    symmetry : Op → Group ℓG
    arity : ∀ op → GroupAction (symmetry op) ℓS


Signature : ∀ ℓG ℓS ℓσ → Type (ℓ-max (ℓ-max (ℓ-suc ℓG) (ℓ-suc ℓS)) (ℓ-suc ℓσ))
Signature ℓG ℓS ℓσ = TypeWithStr ℓσ (SignatureStr ℓG ℓS)

Signature₀ : Type₁
Signature₀ = Signature ℓ-zero ℓ-zero ℓ-zero
