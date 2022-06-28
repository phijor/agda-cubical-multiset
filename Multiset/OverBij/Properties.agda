module Multiset.OverBij.Properties where

open import Multiset.OverBij.Base as OverBij
open import Multiset.Bij as Bij
open import Multiset.Chains
  using
    ( Chain
    ; module Limit
    ; module FunctorChain
    )
open import Multiset.Util.Path
  using
    ( subst⁻-filler
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
    -- ; isShiftedChainLimit to isω⁺Tree
    ; IteratedLimitPathPExt to ωTreePathP
    ; ShiftedLimitPathPExt to ω⁺TreePathP
    )

open ωTree
  renaming
    ( elements to level
    ; isChainLimit to cut
    )

map-level : (FMGpd ωTree) → (n : ℕ) → FMGpd (UnordedTree n)
map-level trees n = map (λ tree → tree .level n) trees

α : (FMGpd ωTree) → ω⁺Tree
α trees@(_ , branches) = Limit.lim (map-level trees) is-limit where

  is-limit : (n : ℕ) → map (!^ n) (map-level trees (suc n)) ≡ map-level trees n
  is-limit n = ΣPathP (refl , funExt (λ (idx : ⟨Bij→FinSet⟩ _) → branches idx .cut n))

module _ (tree⁺@(lim level⁺ levelCoh) : ω⁺Tree) where
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

    level′ : (n : ℕ) → UnordedTree n
    level′ n = branch n (idx n)

    idxPath : ∀ n → PathP (λ i → ⟨Bij→FinSet⟩ (isConstBranchIdx n i)) (idx (suc n)) (idx n)
    idxPath n = symP (subst⁻-filler ⟨Bij→FinSet⟩ (isConstBranchIdx n) (idx n))

    idx₀Path : ∀ n → PathP (λ i → ⟨Bij→FinSet⟩ (isConstBranchIdx₀ n i)) (idx n) idx₀
    idx₀Path zero = refl
    idx₀Path (suc n) = compPathP' {B = ⟨Bij→FinSet⟩} (idxPath n) (idx₀Path n)

    isChainLimitLevel : ∀ n → (!^ n) (level′ (suc n)) ≡ level′ n
    isChainLimitLevel n = cutCohExt n (idx (suc n)) (idx n) (idxPath n)

    open Limit.ChainLimit

    limit : ωTree
    limit .elements = level′
    limit .isChainLimit = isChainLimitLevel

α⁻¹ : ω⁺Tree → (FMGpd ωTree)
α⁻¹ tree⁺ = (branchIdx tree⁺ 0) , limit tree⁺

α∘α⁻¹ : ∀ tree⁺ → α (α⁻¹ tree⁺) ≡ tree⁺
α∘α⁻¹ tree⁺@(lim level⁺ isLimLevel⁺) = ω⁺TreePathP elemPath {!   !} where
  open Limit.ChainLimit

  lemma₁ : ∀ n → branchIdx tree⁺ n ≡ branchIdx tree⁺ 0
  lemma₁ n = isConstBranchIdx₀ tree⁺ n

  lemma₂Ext : ∀ n {idxₙ} {idx₀} (π : PathP (λ i → ⟨Bij→FinSet⟩ (lemma₁ n i)) idxₙ idx₀)
    → level⁺ n .snd idxₙ ≡ level⁺ n .snd (idx tree⁺ idx₀ n)
  lemma₂Ext zero π = refl
  lemma₂Ext (suc n) {idxₙ} {idx₀} π =
    level⁺ (suc n) .snd idxₙ ≡⟨ cong (level⁺ (suc n) .snd) {!   !} ⟩
    level⁺ (suc n) .snd
      (subst⁻ ⟨Bij→FinSet⟩ (isConstBranchIdx tree⁺ n)
       (idx tree⁺ idx₀ n)) ∎

  lemma₂ : ∀ n →
    PathP (λ i → ⟨Bij→FinSet⟩ (lemma₁ n i) → UnordedTree n)
      (level⁺ n .snd)
      (λ idx₀ → level⁺ n .snd (idx tree⁺ idx₀ n))
  lemma₂ n = funExtDep (lemma₂Ext n) -- (λ {x₀ = idxₙ} {x₁ = idx₀} p → cong (level⁺ n .snd) {! idx₀Path tree⁺ idx₀ n  !})

  elemPath : ∀ n → α (α⁻¹ tree⁺) .elements n ≡ tree⁺ .elements n
  elemPath n =
    α (α⁻¹ tree⁺) .elements n ≡⟨⟩
    map (λ tree → tree .level n) (α⁻¹ tree⁺) ≡⟨⟩
    branchIdx tree⁺ 0 , (λ tree → tree .level n) ∘ limit tree⁺ ≡⟨⟩
    branchIdx tree⁺ 0 , (λ idx₀ → level′ tree⁺ idx₀ n) ≡⟨⟩
    branchIdx tree⁺ 0 , (λ idx₀ → branch tree⁺ n (idx tree⁺ idx₀ n)) ≡⟨⟩
    branchIdx tree⁺ 0 , (λ idx₀ → level⁺ n .snd (idx tree⁺ idx₀ n)) ≡⟨ sym (FMGpdPathP (lemma₁ n) (lemma₂ n)) ⟩
    level⁺ n ≡⟨⟩
    tree⁺ .elements n ∎

α⁻¹∘α : (trees : FMGpd ωTree) → α⁻¹ (α trees) ≡ trees
α⁻¹∘α trees@(card , branches) = ΣPathP (refl , branchesPath) where
  open Limit.ChainLimit

  -- TODO: This should follow from idx₀Path
  idxPath′ : ∀ (n : ℕ) (ix : ⟨Bij→FinSet⟩ (branchIdx (α trees) n)) → idx (α trees) ix n ≡ ix
  idxPath′ zero ix = refl
  idxPath′ (suc n) ix = idxPath (α trees) ix n ∙ idxPath′ n ix

  elementsExt : ∀ idx' n → limit (α trees) idx' .elements n ≡ branches idx' .elements n
  elementsExt idx' n = cong (λ ix → branches ix .elements n) (idxPath′ n idx')

  isChainLimitPath : ∀ idx₀ n →
    PathP (λ i → !^ n (elementsExt idx₀ (suc n) i) ≡ elementsExt idx₀ n i)
      (isChainLimitLevel (α trees) idx₀ n)
      _
  isChainLimitPath idx₀ n = compPathP' {!   !} {!   !}

  branchesPathExt : ∀ idx' → snd (α⁻¹ (α trees)) idx' ≡ branches idx'
  branchesPathExt idx' = ωTreePathP (elementsExt idx') (isChainLimitPath idx')

  branchesPath : snd (α⁻¹ (α trees)) ≡ branches
  branchesPath = funExt branchesPathExt

open Iso

αIso : Iso (FMGpd ωTree) ω⁺Tree
αIso .fun = α
αIso .inv = α⁻¹
αIso .rightInv = α∘α⁻¹
αIso .leftInv = α⁻¹∘α

isLimitPreservingFMGpd : FMGpdChain.isLimitPreserving
isLimitPreservingFMGpd = isoToEquiv αIso
