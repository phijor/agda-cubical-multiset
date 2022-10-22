{-# OPTIONS --safe #-}

module Multiset.Tote.Properties where

open import Multiset.Tote.Base as Tote
open import Multiset.FMSet
  using (FMSet ; isSetFMSet ; _∼_ ; SymmetricAction)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.FinSet as FinSet using (FinSet ; isFinSetFin ; isGroupoidFinSet)
open import Cubical.Data.SumFin as Fin
open import Cubical.Data.Nat as ℕ
  using (ℕ ; _+_)

open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming
    ( _/_ to _/₂_
    ; [_] to [_]₂
    ; eq/ to eq/₂
    )
open import Cubical.HITs.SetTruncation as ST
  using
    ( ∥_∥₂
    ; ∣_∣₂
    ; squash₂
    ; isSetSetTrunc
    )
open import Cubical.HITs.PropositionalTruncation as PT
  renaming
    ( ∥_∥₁ to ∥_∥
    ; ∣_∣₁ to ∣_∣
    )

private
  variable
    ℓ : Level
    X : Type ℓ

isGroupoidTote : isGroupoid X → isGroupoid (Tote X)
isGroupoidTote h = isOfHLevelΣ 3 isGroupoidFinSet λ _ → isOfHLevelΠ 3 (λ _ → h)

isOfHLevel₊₃Tote : (n : ℕ) → (isOfHLevel (3 + n) X) → isOfHLevel (3 + n) (Tote X)
isOfHLevel₊₃Tote n h = isOfHLevelΣ (3 + n) lem λ _ → isOfHLevelΠ (3 + n) (λ _ → h) where
  lem : ∀ {ℓ} → isOfHLevel (3 + n) (FinSet ℓ)
  lem = subst (λ k → isOfHLevel k (FinSet _)) (ℕ.+-comm n 3) (isOfHLevelPlus n FinSet.isGroupoidFinSet)

open Iso

FMSet→∥Tote∥₂ : FMSet X → ∥ Tote X ∥₂
FMSet→∥Tote∥₂ (n , x) = SQ.rec squash₂ f well-defined x where
  f : (Fin n → X) → ∥ Tote X ∥₂
  f v = ∣ (Fin n , isFinSetFin) , v ∣₂

  well-defined : (v w : Fin n → X) → v ∼ w → f v ≡ f w
  well-defined v w = PT.elim
    (λ _ → isSetSetTrunc _ _)
    (λ (σ , v∘σ≡w) → cong ∣_∣₂ (TotePath (ua σ) v∘σ≡w))

Tote→FMSet : Tote X → FMSet X
Tote→FMSet {X = X} ((Y , n , e) , v) = n , (PT.rec→Set SQ.squash/ from-equiv is2Const e) where
  from-equiv : Y ≃ Fin n → (Fin n → X) /₂ SymmetricAction n
  from-equiv α = [ v ∘ invEq α ]₂

  is2Const : (α β : Y ≃ Fin n) → [ v ∘ (invEq α) ]₂ ≡ [ v ∘ (invEq β) ]₂
  is2Const α β = SQ.eq/ {R = SymmetricAction n} _ _ ∣ σ , (ua→ step₂) ∣ where
    σ : Fin n ≃ Fin n
    σ = invEquiv α ∙ₑ β

    α⁻ = invEq α
    β⁺ = equivFun β
    β⁻ = invEq β

    module _ (k : Fin n) where
      step₁ : α⁻ k ≡ β⁻ (β⁺ (α⁻ k))
      step₁ = sym (retEq β (α⁻ k))

      step₂ : v (α⁻ k) ≡ v (β⁻ (β⁺ (α⁻ k)))
      step₂ = cong v step₁

∥Tote∥₂→FMSet : ∥ Tote X ∥₂ → FMSet X
∥Tote∥₂→FMSet = ST.rec isSetFMSet Tote→FMSet

-- Section
∥Tote∥₂→FMSet→∥Tote∥₂ : (x : ∥ Tote X ∥₂) → FMSet→∥Tote∥₂ (∥Tote∥₂→FMSet x) ≡ x
∥Tote∥₂→FMSet→∥Tote∥₂ {X = X} = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _)) go where

  module _ (Y : Type) (n : ℕ) (v : Y → X) (α : Y ≃ Fin n) where
    equiv-path :
      (λ i → ∥ ua (invEquiv α) i ≃ Fin n ∥) [ ∣ idEquiv (Fin n) ∣ ≡ ∣ α ∣ ]
    equiv-path = isProp→PathP (λ i → PT.isPropPropTrunc) _ _

    is-permutation : ∀ k → (v ∘ invEq α) k ≡ v (invEq α k)
    is-permutation _ = refl

    sect : ∣ (Fin n , n , ∣ idEquiv (Fin n) ∣) , v ∘ invEq α ∣₂ ≡ ∣ (Y , n , ∣ α ∣) , v ∣₂
    sect = cong ∣_∣₂ (TotePathP≃ (invEquiv α) is-permutation)

  f : ∥ Tote X ∥₂ → ∥ Tote X ∥₂
  f x = FMSet→∥Tote∥₂ (∥Tote∥₂→FMSet x)

  -- Proof by induction on the propositionally truncated
  -- equivalence (e : ∥ Y ≃ Fin k ∥):
  go : (x : Tote X) → f ∣ x ∣₂ ≡ ∣ x ∣₂
  go ((Y , n , e) , v) = PT.elim
    -- Equality in a set truncation is a proposition:
    (λ α → let x = ∣ (Y , n , α) , v ∣₂ in squash₂ (f x) x)
    (sect Y n v)
    e

FMSet→∥Tote∥₂→FMSet : (x : FMSet X) → ∥Tote∥₂→FMSet (FMSet→∥Tote∥₂ x) ≡ x
FMSet→∥Tote∥₂→FMSet (n , v) = SQ.elimProp
  {P = λ v → ∥Tote∥₂→FMSet (FMSet→∥Tote∥₂ (n , v)) ≡ (n , v)}
  (λ _ → isSetFMSet _ _)
  (λ v → refl)
  v

FMSet-∥Tote∥₂-Iso : Iso (FMSet X) (∥ Tote X ∥₂)
FMSet-∥Tote∥₂-Iso .fun = FMSet→∥Tote∥₂
FMSet-∥Tote∥₂-Iso .inv = ∥Tote∥₂→FMSet
FMSet-∥Tote∥₂-Iso .rightInv = ∥Tote∥₂→FMSet→∥Tote∥₂
FMSet-∥Tote∥₂-Iso .leftInv = FMSet→∥Tote∥₂→FMSet

FMSet≃∥Tote∥₂ : FMSet X ≃ ∥ Tote X ∥₂
FMSet≃∥Tote∥₂ = isoToEquiv FMSet-∥Tote∥₂-Iso
