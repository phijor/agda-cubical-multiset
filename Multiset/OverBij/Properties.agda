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

open module BagChain = FunctorChain Bag (OverBij.map) Unit (! _)
  using ()
  renaming
    ( iterObj to UnordedTree
    ; iterInit to !^
    ; IteratedLimit to ωTree -- Limit over the chain starting at Unit
    ; ShiftedLimit to ω⁺Tree -- Limit over the chain starting at (Bag Unit)
    -- ; isShiftedChainLimit to isω⁺Tree
    ; IteratedLimitPathPExt to ωTreePathP
    ; ShiftedLimitPathPExt to ω⁺TreePathP
    )

open ωTree
  renaming
    ( elements to level
    ; isChainLimit to cut
    )

open Bag

map-level : (Bag ωTree) → (n : ℕ) → Bag (UnordedTree n)
map-level trees n = map (λ tree → tree .level n) trees

α : (Bag ωTree) → ω⁺Tree
α trees = Limit.lim (map-level trees) is-limit where

  is-limit : (n : ℕ) → map (!^ n) (map-level trees (suc n)) ≡ map-level trees n
  is-limit n = BagPathExt (λ idx → trees .members idx .cut n)

module _ (tree⁺@(lim level⁺ levelCoh) : ω⁺Tree) where
  _ : (n : ℕ) → Bag (UnordedTree n)
  _ = level⁺

  branchIdx : (n : ℕ) → Bij
  branchIdx n = level⁺ n .card

  branch : (n : ℕ) → (Idx (branchIdx n) → UnordedTree n)
  branch n = level⁺ n .members

  isConstBranchIdx : ∀ n → branchIdx (suc n) ≡ branchIdx n
  isConstBranchIdx n = cong card (levelCoh n)

  isConstBranchIdx₀ : ∀ n → branchIdx n ≡ branchIdx 0
  isConstBranchIdx₀ zero = refl
  isConstBranchIdx₀ (suc n) = isConstBranchIdx n ∙ isConstBranchIdx₀ n

  cutCoh : ∀ n → PathP (λ i → Idx (isConstBranchIdx n i) → UnordedTree n)
    (!^ n ∘ branch (suc n)) (branch n)
  cutCoh n = cong members (levelCoh n)

  cutCohExt : ∀ n idx₀ idx₁
    → PathP (λ i → Idx (isConstBranchIdx n i)) idx₀ idx₁
    → !^ n (branch (suc n) idx₀) ≡ branch n idx₁
  cutCohExt n idx₀ idx₁ = funExtDep⁻ (cutCoh n)

  module _ (idx₀ : Idx (branchIdx 0)) where

    idx : (n : ℕ) → Idx (branchIdx n)
    idx zero = idx₀
    idx (suc n) = subst⁻ Idx (isConstBranchIdx n) (idx n)

    level′ : (n : ℕ) → UnordedTree n
    level′ n = branch n (idx n)

    idxPath : ∀ n → PathP (λ i → Idx (isConstBranchIdx n i)) (idx (suc n)) (idx n)
    idxPath n = symP (subst⁻-filler Idx (isConstBranchIdx n) (idx n))

    idx₀Path : ∀ n → PathP (λ i → Idx (isConstBranchIdx₀ n i)) (idx n) idx₀
    idx₀Path zero = refl
    idx₀Path (suc n) = compPathP' {B = Idx} (idxPath n) (idx₀Path n)

    isChainLimitLevel : ∀ n → (!^ n) (level′ (suc n)) ≡ level′ n
    isChainLimitLevel n = cutCohExt n (idx (suc n)) (idx n) (idxPath n)

    open Limit.ChainLimit

    limit : ωTree
    limit .elements = level′
    limit .isChainLimit = isChainLimitLevel

α⁻¹ : ω⁺Tree → (Bag ωTree)
α⁻¹ tree⁺ = ⟅ limit tree⁺ ⟆

α∘α⁻¹ : ∀ tree⁺ → α (α⁻¹ tree⁺) ≡ tree⁺
α∘α⁻¹ tree⁺@(lim level⁺ isLimLevel⁺) = ω⁺TreePathP elemPath {!   !} where
  open Limit.ChainLimit

  lemma₁ : ∀ n → branchIdx tree⁺ n ≡ branchIdx tree⁺ 0
  lemma₁ n = isConstBranchIdx₀ tree⁺ n

  lemma₂Ext : ∀ n {idxₙ} {idx₀} (π : PathP (λ i → Idx (lemma₁ n i)) idxₙ idx₀)
    → level⁺ n .members idxₙ ≡ level⁺ n .members (idx tree⁺ idx₀ n)
  lemma₂Ext zero π = refl
  lemma₂Ext (suc n) {idxₙ} {idx₀} π =
    level⁺ (suc n) .members idxₙ ≡⟨ cong (level⁺ (suc n) .members) {!   !} ⟩
    level⁺ (suc n) .members
      (subst⁻ Idx (isConstBranchIdx tree⁺ n)
       (idx tree⁺ idx₀ n)) ∎

  lemma₂ : ∀ n →
    PathP (λ i → Idx (lemma₁ n i) → UnordedTree n)
      (level⁺ n .members)
      (λ idx₀ → level⁺ n .members (idx tree⁺ idx₀ n))
  lemma₂ n = funExtDep (lemma₂Ext n) -- (λ {x₀ = idxₙ} {x₁ = idx₀} p → cong (level⁺ n .snd) {! idx₀Path tree⁺ idx₀ n  !})

  elemPath : ∀ n → α (α⁻¹ tree⁺) .elements n ≡ tree⁺ .elements n
  elemPath n =
    α (α⁻¹ tree⁺) .elements n ≡⟨⟩
    map (λ tree → tree .level n) (α⁻¹ tree⁺) ≡⟨⟩
    ⟅ (λ tree → tree .level n) ∘ limit tree⁺ ⟆ ≡⟨⟩
    ⟅ idx₀ ↦ level′ tree⁺ idx₀ n ⟆ ≡⟨⟩
    ⟅ idx₀ ↦ branch tree⁺ n (idx tree⁺ idx₀ n) ⟆ ≡⟨⟩
    ⟅ idx₀ ↦ level⁺ n .members (idx tree⁺ idx₀ n) ⟆ ≡⟨ sym (BagPathP (lemma₁ n) (lemma₂ n)) ⟩
    level⁺ n ≡⟨⟩
    tree⁺ .elements n ∎

α⁻¹∘α : (trees : Bag ωTree) → α⁻¹ (α trees) ≡ trees
α⁻¹∘α trees@(⟅ branches ⟆) = BagPath branchesPath where
  open Limit.ChainLimit

  -- TODO: This should follow from idx₀Path
  idxPath′ : ∀ (n : ℕ) (ix : Idx (branchIdx (α trees) n)) → idx (α trees) ix n ≡ ix
  idxPath′ zero ix = refl
  idxPath′ (suc n) ix = idxPath (α trees) ix n ∙ idxPath′ n ix

  elementsExt : ∀ idx' n → limit (α trees) idx' .elements n ≡ branches idx' .elements n
  elementsExt idx' n = cong (λ ix → branches ix .elements n) (idxPath′ n idx')

  isChainLimitPath : ∀ idx₀ n →
    PathP (λ i → !^ n (elementsExt idx₀ (suc n) i) ≡ elementsExt idx₀ n i)
      (isChainLimitLevel (α trees) idx₀ n)
      _
  isChainLimitPath idx₀ n = compPathP' {!   !} {!   !}

  branchesPathExt : ∀ idx' → (α⁻¹ (α trees)) .members idx' ≡ branches idx'
  branchesPathExt idx' = ωTreePathP (elementsExt idx') (isChainLimitPath idx')

  _ : (α⁻¹ (α trees)) .members ≡ limit (α trees)
  _ = refl

  branchesPath : (α⁻¹ (α trees)) .members ≡ branches
  branchesPath = funExt branchesPathExt

open Iso

αIso : Iso (Bag ωTree) ω⁺Tree
αIso .fun = α
αIso .inv = α⁻¹
αIso .rightInv = α∘α⁻¹
αIso .leftInv = α⁻¹∘α

isLimitPreservingBag : BagChain.isLimitPreserving
isLimitPreservingBag = isoToEquiv αIso
