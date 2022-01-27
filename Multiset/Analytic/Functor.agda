module Multiset.Analytic.Functor where

open import Cubical.Foundations.Prelude renaming (funExt⁻ to happly)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Nat.Base
open import Cubical.Data.Fin.Base
open import Cubical.Algebra.Group.Base

open import Cubical.HITs.TypeQuotients.Base

open import Multiset.GroupAction.Base
open import Multiset.GroupAction.Induced
open import Multiset.GroupAction.Orbit
open import Multiset.Analytic.Base

private
  variable
    ℓ ℓG ℓX ℓY ℓZ ℓσ : Level

module Functor (Sig : Signature ℓσ ℓG) where
  module _ (X : Type ℓX) (σ : ⟨ Sig ⟩) where
    private
      open module Sig = SignatureStr (str Sig)

      Gσ : Group _
      Gσ = Action σ .fst

    coordAction : GroupAction (Sig.Action σ .fst) ℓX
    coordAction = Induced (permutationActionToAction (Action σ)) X

    --- Define the set of orbits X^σ/∼ where...
    ---
    --- * X is some type
    --- * X^σ is X to the power of the arity of an operation σ
    --- * ∼ is the orbit relation on X^σ under coordinate permutation,
    ---   as induced by G.
    _^_/∼ : Type (ℓ-max ℓG ℓX)
    _^_/∼ = Orbit coordAction

  _/∼ : (X : Type ℓX) → Type _
  _/∼ {ℓX = ℓX} X = Σ[ σ ∈ ⟨ Sig ⟩ ] ( X ^ σ /∼ )

  private
    variable
      X : Type ℓX
      Y : Type ℓY
      Z : Type ℓZ

  _^_/ₘ∼ : (f : X → Y) (σ : ⟨ Sig ⟩) → (X ^ σ /∼ → Y ^ σ /∼)
  _^_/ₘ∼ f σ = OrbitMap.descend Sσ f where
    open SignatureStr (str Sig)

    Gσ : Group ℓG
    Gσ = Action σ .fst

    Sσ : GroupAction Gσ ℓ-zero
    Sσ = permutationActionToAction (Action σ)

  id-/∼ : (σ : ⟨ Sig ⟩) → (idfun X) ^ σ /ₘ∼ ≡ idfun (X ^ σ /∼)
  id-/∼ {X = X} σ = descend-id _ _

  comp-/∼ : (σ : ⟨ Sig ⟩)
    → (f : X → Y) (g : Y → Z)
    → (g ∘ f) ^ σ /ₘ∼ ≡ (g ^ σ /ₘ∼) ∘ (f ^ σ /ₘ∼)
  comp-/∼ σ f g = descend-comp _ f g

module Example where
  open import Cubical.HITs.TypeQuotients.Base

  open import Multiset.GroupAction.Instances

  private
    arity : ℕ → ℕ
    arity n = n

  OrderedTreesSignature : Signature ℓ-zero ℓ-zero
  OrderedTreesSignature = ℕ , signaturestr arity UnitPermAction

  UnorderedTreesSignature : Signature ℓ-zero ℓ-zero
  UnorderedTreesSignature = ℕ , signaturestr arity SymPermAction

  open Functor UnorderedTreesSignature

  ex₁ : Type → Type
  ex₁ X =  X ^ 2 /∼

  ex₂ : (X : Type) (x₀ x₁ : X) → X /∼
  ex₂ X x₀ x₁ = 2 , [ v ]  where
    open import Cubical.Data.Nat.Order

    v : Fin 2 → X
    v (0 , _) = x₀
    v (1 , _) = x₁
    v (suc (suc k) , k' , p) = {! !}
