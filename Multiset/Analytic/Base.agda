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

--- Define the set of orbits X^k/∼G where...
---
--- * X is some type
--- * k is the arity of the operation `op`
--- * ∼G is the orbit relation on X^k under coordinate permutation,
---   as induced by G.
Orbit : {ℓX : Level} (X : Type ℓX) {σ : Signature ℓσ ℓG} (op : ⟨ σ ⟩)
  → Type (ℓ-max ℓG ℓX)
Orbit X {σ} op = X^op/G_op
  where
    import Multiset.GroupAction.Induced
    import Multiset.GroupAction.Orbit

    module Sig = SignatureStr (str σ)
    module opAction = Multiset.GroupAction.Induced.Induced (permutationActionToAction (Sig.Action op))

    G_op : Group _
    G_op = Sig.Action op .fst

    coordAction : GroupAction (Opposite.OppositeGroup (G_op)) _
    coordAction = opAction.Induced X

    open module coordOrbit = Orbit coordAction renaming (S/G to X^op/G_op)
