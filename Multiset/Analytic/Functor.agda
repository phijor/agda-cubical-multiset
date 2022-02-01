module Multiset.Analytic.Functor where

open import Cubical.Foundations.Prelude renaming (funExt⁻ to happly)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
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
    ℓG ℓS ℓX ℓY ℓZ ℓσ : Level

module Functor (Sig : Signature ℓG ℓS ℓσ) where
  module _ (X : Type ℓX) (σ : ⟨ Sig ⟩) where
    private
      open module Sig = SignatureStr (str Sig)

    -- coordAction : GroupAction (Sig.Action σ .fst) ℓX
    coordAction = Induced (arity σ) X


    --- Define the set of orbits X^σ/∼ where...
    ---
    --- * X is some type
    --- * X^σ is X to the power of the arity of an operation σ
    --- * ∼ is the orbit relation on X^σ under coordinate permutation,
    ---   as induced by G.
    _^_/∼ : Type (ℓ-max (ℓ-max ℓG ℓS) ℓX)
    _^_/∼ = Orbit coordAction

  _/∼ : (X : Type ℓX) → Type _
  _/∼ {ℓX = ℓX} X = Σ[ σ ∈ ⟨ Sig ⟩ ] ( X ^ σ /∼ )

  private
    variable
      X : Type ℓX
      Y : Type ℓY
      Z : Type ℓZ

  _^_/ₘ∼ : (f : X → Y) (σ : ⟨ Sig ⟩) → (X ^ σ /∼ → Y ^ σ /∼)
  _^_/ₘ∼ f σ = OrbitMap.descend (arity σ) f where
    open SignatureStr (str Sig)

    -- Gσ : Group ℓG
    -- Gσ = Action σ .fst

    -- Sσ : GroupAction Gσ ℓ-zero
    -- Sσ = permutationActionToAction (Action σ)

  _/ₘ∼ : (f : X → Y) → (X /∼ → Y /∼)
  (f /ₘ∼) (σ , x) = σ , (f ^ σ /ₘ∼) x

  id-/∼ : (idfun X) /ₘ∼ ≡ idfun (X /∼)
  id-/∼ {X = X} = λ i (σ , x) → σ , aux σ i x where
    aux : (σ : ⟨ Sig ⟩) → (idfun X) ^ σ /ₘ∼ ≡ idfun (X ^ σ /∼)
    aux σ = descend-id _ _

  comp-/ₘ∼ : (f : X → Y) → (g : Y → Z)
    → (g ∘ f) /ₘ∼ ≡ g /ₘ∼ ∘ f /ₘ∼
  comp-/ₘ∼ f g = λ i (σ , x) → σ , aux σ i x where
    aux : (σ : ⟨ Sig ⟩) → (g ∘ f) ^ σ /ₘ∼ ≡ (g ^ σ /ₘ∼) ∘ (f ^ σ /ₘ∼)
    aux σ = descend-comp _ f g

module Chain (Sig : Signature ℓG ℓS ℓσ) where
  open import Multiset.Chains

  private
    variable
      ℓ : Level

    open module F = Functor Sig
    open Chain
    open Limit
    open ChainLimit

  apChain : (X : Chain ℓ) → Chain (ℓ-max (ℓ-max (ℓ-max ℓG ℓS) ℓσ) ℓ)
  apChain X = chain ((_/∼) ∘ X .Ob) ((_/ₘ∼) ∘ X .π)

  α : {X : Chain ℓ}
    → (ChainLimit X) /∼ → ChainLimit (apChain X)
  α {X = X} (σ , [ v ]) = lim
    (λ n → σ , [ w n ]) (λ n → ΣPathP ( refl , lemma₂ n )) where
      open module Sig = SignatureStr (str Sig)
      open module Gσ = GroupStr (str (symmetry σ))

      w : (n : ℕ) → ⟨ arity σ ⟩ → X .Ob n
      w n k = v k .proj n

      module _ (n : ℕ) where
        Sσ = coordAction (X .Ob n) σ
        open module Sσ = GroupActionStr (str Sσ)

        lemma₁ : (X .π n) ∘ (w (suc n)) ≡ w n
        lemma₁ = funExt λ k → v k .isChainLimit n

        lemma₂ : [ (X .π n) ∘ (w (suc n)) ] ≡ [ w n ]
        lemma₂ = Path→OrbitPath Sσ lemma₁
  α (σ , eq/ v w r i) = lemma i where
    lemma : α (σ , [ v ]) ≡ α (σ , [ w ])
    lemma = {!   !}

module Example where
  open import Cubical.HITs.TypeQuotients.Base
  open import Cubical.Algebra.SymmetricGroup
  open import Cubical.Algebra.Group.Instances.Unit renaming (Unit to UnitGroup)

  open import Multiset.GroupAction.Instances

  private
    arity : ℕ → ℕ
    arity n = n

  OrderedTreesSignature : Signature₀
  OrderedTreesSignature = ℕ , signaturestr (λ _ → UnitGroup) λ n → UnitAction (Fin n)

  UnorderedTreesSignature : Signature₀
  UnorderedTreesSignature =  ℕ , signaturestr Sym SymAction

  open Functor UnorderedTreesSignature

  ex₁ : Type → Type
  ex₁ X =  X ^ 2 /∼

  vec₂ : {X : Type} (x₀ x₁ : X) → Fin 2 → X
  vec₂ x₀ _ (0 , _) = x₀
  vec₂ _ x₁ (1 , _) = x₁
  vec₂ _ _ _ = {!   !}

  ex₂ : {X : Type} (x₀ x₁ : X) → X /∼
  ex₂ {X = X} x₀ x₁ = 2 , [ vec₂ x₀ x₁ ]

  ex₂-swap : {X : Type} (x₀ x₁ : X) → ex₂ x₀ x₁ ≡ ex₂ x₁ x₀
  ex₂-swap {X = X} x₀ x₁ = ΣPathP (refl , eq/ (vec₂ x₀ x₁) (vec₂ x₁ x₀) swap)
    where
      open import Cubical.Data.Sigma

      swap-impl : Fin 2 → Fin 2
      swap-impl (zero , _) = (suc zero , (0 , refl))
      swap-impl (suc zero , _) = (zero , (1 , refl))
      swap-impl (suc (suc _) , _) = {!  !}

      do-swap : ∀ s → vec₂ x₀ x₁ (swap-impl s) ≡ vec₂ x₁ x₀ s
      do-swap (zero , snd₁) = refl
      do-swap (suc zero , snd₁) = refl
      do-swap (suc (suc fst₁) , snd₁) = {!   !}

      swap : reachable (Induced (SymAction 2) X) (vec₂ x₀ x₁) (vec₂ x₁ x₀)
      swap = (swap-impl , {! isEquiv swap-impl  !}) , funExt do-swap
