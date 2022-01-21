module Multiset.Analytic.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Base

open import Multiset.GroupAction.Base

private
  variable
    ℓ ℓG ℓσ : Level

record SignatureStr (ℓG : Level) (Op : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓG)) where

  constructor signaturestr

  field
    arity : Op → ℕ
    Action : ∀ op → PermutationAction (arity op) ℓG


Signature : ∀ ℓσ ℓG → Type (ℓ-suc (ℓ-max ℓσ ℓG))
Signature ℓσ ℓG = TypeWithStr ℓσ (SignatureStr ℓG)
