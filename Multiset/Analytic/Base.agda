module Multiset.Analytic.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat hiding (Unit)
open import Cubical.Data.Sigma
open import Cubical.Data.Fin
open import Cubical.Algebra.Group

open import Multiset.GroupAction

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

module _ where
  import Multiset.GroupAction.Instances

  open Multiset.GroupAction.Instances.FinPermutation

  private
    arity : ℕ → ℕ
    arity n = n

  OrderedTreesSignature : Signature ℓ-zero ℓ-zero
  OrderedTreesSignature = ℕ , signaturestr arity UnitPermAction

  UnorderedTreesSignature : Signature ℓ-zero ℓ-zero
  UnorderedTreesSignature = ℕ , signaturestr arity SymPermAction
