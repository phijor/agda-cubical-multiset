module Multiset.OverBij.Properties where

open import Multiset.OverBij.Base as OverBij
open import Multiset.Bij as Bij
open import Multiset.Chains
  using
    ( Chain
    ; module Limit
    ; module FunctorChain
    )

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (subst⁻ ; transport⁻-filler)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Functions.FunExtEquiv using (funExtDep ; funExtDep⁻)

open import Cubical.Data.Sigma as Σ
  using (ΣPathP)
open import Cubical.Data.Nat as ℕ
  using (ℕ ; zero ; suc)
open import Cubical.Data.Unit as Unit
  using
    ( Unit
    ; tt
    )

private
  variable
    ℓ : Level

!_ : (A : Type ℓ) → A → Unit
! A = λ a → tt

open Limit using (lim)

open module FMGpdChain = FunctorChain FMGpd (OverBij.map) Unit (! _)
  using ()
  renaming
    ( iterObj to UnordedTree
    ; iterInit to !^
    ; IteratedLimit to ωTree -- Limit over the chain starting at Unit
    ; ShiftedLimit to ω⁺Tree -- Limit over the chain starting at (FMGpd Unit)
    ; ShiftedLimitPathPExt to ω⁺TreePathP
    )

α : (FMGpd ωTree) → ω⁺Tree
α trees@(_ , branches) = Limit.lim shifted-elements is-limit where

  open ωTree
    renaming
      ( elements to level
      ; isChainLimit to cut
      )

  shifted-elements : (n : ℕ) → FMGpd (UnordedTree n)
  shifted-elements n = map (λ tree → tree .level n) trees

  is-limit : (n : ℕ) → map (!^ n) (shifted-elements (suc n)) ≡ shifted-elements n
  is-limit n = ΣPathP (refl , funExt (λ (idx : ⟨Bij→FinSet⟩ _) → branches idx .cut n))

α⁻¹ : ω⁺Tree → (FMGpd ωTree)
α⁻¹ tree⁺@(lim level⁺ levelCoh) = (branchIdx 0) , (λ idx → lim (level idx) (isChainLimitLevel idx)) where
  _ : (n : ℕ) → FMGpd (UnordedTree n)
  _ = level⁺

  branchIdx : (n : ℕ) → Bij
  branchIdx n = level⁺ n .fst

  branch : (n : ℕ) → (⟨Bij→FinSet⟩ (branchIdx n) → UnordedTree n)
  branch n = level⁺ n .snd

  isConstBranchIdx : ∀ n → branchIdx (suc n) ≡ branchIdx n
  isConstBranchIdx n = cong fst (levelCoh n)

  isConstBranchIdx₀ : ∀ n → branchIdx n ≡ branchIdx 0
  isConstBranchIdx₀ zero = refl
  isConstBranchIdx₀ (suc n) = isConstBranchIdx n ∙ isConstBranchIdx₀ n

  cutCoh : ∀ n → PathP (λ i → ⟨Bij→FinSet⟩ (isConstBranchIdx n i) → UnordedTree n)
    (!^ n ∘ branch (suc n)) (branch n)
  cutCoh n = cong snd (levelCoh n)

  cutCohExt : ∀ n idx₀ idx₁
    → PathP (λ i → ⟨Bij→FinSet⟩ (isConstBranchIdx n i)) idx₀ idx₁
    → !^ n (branch (suc n) idx₀) ≡ branch n idx₁
  cutCohExt n idx₀ idx₁ = funExtDep⁻ (cutCoh n)

  module _ (idx₀ : ⟨Bij→FinSet⟩ (branchIdx 0)) where

    idx : (n : ℕ) → ⟨Bij→FinSet⟩ (branchIdx n)
    idx zero = idx₀
    idx (suc n) = subst⁻ ⟨Bij→FinSet⟩ (isConstBranchIdx n) (idx n)

    level : (n : ℕ) → UnordedTree n
    level n = branch n (idx n)

    idxPath : ∀ n → PathP (λ i → ⟨Bij→FinSet⟩ (isConstBranchIdx n i)) (idx (suc n)) (idx n)
    idxPath n = symP (transport⁻-filler (cong ⟨Bij→FinSet⟩ ((isConstBranchIdx n))) (idx n))

    isChainLimitLevel : ∀ n → (!^ n) (level (suc n)) ≡ level n
    isChainLimitLevel n = cutCohExt n (idx (suc n)) (idx n) (idxPath n)

α∘α⁻¹ : ∀ tree⁺ → α (α⁻¹ tree⁺) ≡ tree⁺
α∘α⁻¹ tree⁺@(lim level⁺ _) = ω⁺TreePathP elemPath {!   !} where
  open Limit.ChainLimit

  elemPath : ∀ n → α (α⁻¹ tree⁺) .elements n ≡ tree⁺ .elements n
  elemPath n =
    α (α⁻¹ tree⁺) .elements n ≡⟨ {!   !} ⟩
    level⁺ n ≡⟨⟩
    tree⁺ .elements n ∎

α⁻¹∘α : (trees : FMGpd ωTree) → α⁻¹ (α trees) ≡ trees
α⁻¹∘α trees@(_ , branches) = ΣPathP (refl , {!   !}) where
  branchesPath : snd (α⁻¹ (α (_ , branches))) ≡ branches
  branchesPath =
    snd (α⁻¹ (α (_ , branches))) ≡⟨ {!   !} ⟩
    branches ∎

open Iso

αIso : Iso (FMGpd ωTree) ω⁺Tree
αIso .fun = α
αIso .inv = α⁻¹
αIso .rightInv = α∘α⁻¹
αIso .leftInv = α⁻¹∘α

isLimitPreservingFMGpd : FMGpdChain.isLimitPreserving
isLimitPreservingFMGpd = isoToEquiv αIso
