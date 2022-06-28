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
open import Multiset.Util.Square using (kiteFiller)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
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
    ; ShiftedLimit to ωBagOfTrees -- Limit over the chain (lim (n ↦ Bag (UnordedTree n))
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

BagUnit≃Bij : Bag Unit ≃ Bij
BagUnit≃Bij = isoToEquiv BagIsoΣ ∙ₑ Σ.Σ-contractSnd {B = λ (x : Bij) → Idx x → Unit} (λ _ → isContrΠUnit) where
  isContrΠUnit : {X : Type} → isContr (X → Unit)
  isContrΠUnit {X} = (! X) , λ f → refl

-- Zipping and unzipping non-wellfounded trees

{- Unzipping

Given a bag of non-wellfounded trees, we can "unzip" it into
a limiting sequences of bags of trees.

At step n in the sequence, the resulting bag contains a tree
of depth n, obtained by mapping the "cut at depth n"-function
over the input bag.
-}
module Unzip (trees : Bag ωTree) where
  bagAt : (n : ℕ) → Bag (UnordedTree n)
  bagAt n = map (λ tree → tree .level n) trees

  isChainLimitBags : (n : ℕ) → map (!^ n) (bagAt (suc n)) ≡ bagAt n
  isChainLimitBags n = BagPathExt (λ idx → trees .members idx .cut n)

  unzipped : ωBagOfTrees
  unzipped = lim bagAt isChainLimitBags

α : (Bag ωTree) → ωBagOfTrees
α trees = Unzip.unzipped trees

{- Zipping

Given a limit over a sequence of bags of trees, we can perform a "zipping"
operation that is dual to unzipping:

From such a limiting sequence, we obtain a bag of trees (`zipped`).
The cardinality of the bag is the same as the cardinality of the
bag at index 0 in the chain (`card₀`).  Indeed, we can show that
the cardinality of bags along the chain remains constant (`isConstCard`).

To build the members of the final bag, we're given an index `idx₀ : card₀`,
which we can substitute by an index into any bag along the chain (`idxAt`).
Thus we obtain, for each step `n`, a tree of depth n by indexing into the
nᵗʰ bag (tree).  For each index, this chain of trees is a limit, giving us
a bag of ωTrees.
-}
module Zip (tree⁺ : ωBagOfTrees) where
  open ωBagOfTrees
    renaming (elements to step ; isChainLimit to stepCoh)

  _ : (n : ℕ) → Bag (UnordedTree n)
  _ = tree⁺ .step

  -- Each step in the chain is a bag of a certain cardinality.
  cardAt : (n : ℕ) → Bij
  cardAt n = tree⁺ .step n .card

  card₀ : Bij
  card₀ = cardAt 0

  -- All bags in the chain have the same cardinality.
  isConstCardSuc : ∀ n → cardAt (suc n) ≡ cardAt n
  isConstCardSuc n = cong card (tree⁺ .stepCoh n)

  isConstCard : ∀ n → cardAt n ≡ card₀
  isConstCard zero = refl
  isConstCard (suc n) = isConstCardSuc n ∙ isConstCard n

  -- We can index the bag at step n to obtain a tree of depth n.
  treesAt : (n : ℕ) → (Idx (cardAt n) → UnordedTree n)
  treesAt n = tree⁺ .step n .members

  -- These trees are related to eachother.  Chopping of the last
  -- level of a tree at step n+1 yields the corresponding tree of
  -- at the same index in step n.
  cutCoh : ∀ n → PathP (λ i → Idx (isConstCardSuc n i) → UnordedTree n)
    (!^ n ∘ treesAt (suc n)) (treesAt n)
  cutCoh n = cong members (tree⁺ .stepCoh n)

  cutCohExt : ∀ n idx₀ idx₁
    → PathP (λ i → Idx (isConstCardSuc n i)) idx₀ idx₁
    → !^ n (treesAt (suc n) idx₀) ≡ treesAt n idx₁
  cutCohExt n idx₀ idx₁ = funExtDep⁻ (cutCoh n)

  -- Assuming we're given an index into the first bag, we can build
  -- a non-wellfounded tree from all the (wellfounded) trees at the
  -- corresponding indices up the chain of bags:
  module _ (idx₀ : Idx card₀) where

    -- All bags have the same cardinality, so convert idx₀ into an
    -- index into the nᵗʰ bag along the chain.
    idxAt : (n : ℕ) → Idx (cardAt n)
    idxAt zero = idx₀
    idxAt (suc n) = subst⁻ Idx (isConstCardSuc n) (idxAt n)

    -- Yes, these indices are indeed the same.
    -- TODO: Can we omit this and use `isConstCard` directly in the
    -- definitions below?
    idxPath : ∀ n → PathP (λ i → Idx (isConstCardSuc n i)) (idxAt (suc n)) (idxAt n)
    idxPath n = symP (subst⁻-filler Idx (isConstCardSuc n) (idxAt n))

    -- We use idxAt to get a tree of depth n from the nᵗʰ bag:
    zippedTrees : (n : ℕ) → UnordedTree n
    zippedTrees n = treesAt n (idxAt n)

    -- TODO: Same as above, can we get rid of this and use isConstCard directly?
    idx₀Path : ∀ n → PathP (λ i → Idx (isConstCard n i)) (idxAt n) idx₀
    idx₀Path zero = refl
    idx₀Path (suc n) = compPathP' {B = Idx} (idxPath n) (idx₀Path n)

    -- This sequence of trees does indeed form a limit:
    isChainLimitZippedTrees : ∀ n → (!^ n) (zippedTrees (suc n)) ≡ zippedTrees n
    isChainLimitZippedTrees n = cutCohExt n (idxAt (suc n)) (idxAt n) (idxPath n)

    open Limit.ChainLimit

    zippedTree : ωTree
    zippedTree .elements = zippedTrees
    zippedTree .isChainLimit = isChainLimitZippedTrees

  zipped : Bag ωTree
  zipped = ⟅ zippedTree idx₀ ∣ idx₀ ∈ card₀ ⟆

α⁻¹ : ωBagOfTrees → (Bag ωTree)
α⁻¹ tree⁺ = Zip.zipped tree⁺

α∘α⁻¹ : ∀ tree⁺ → α (α⁻¹ tree⁺) ≡ tree⁺
α∘α⁻¹ tree⁺@(lim level⁺ isLimLevel⁺) = ω⁺TreePathP elemPath {!   !} where
  open Limit.ChainLimit

  open Zip tree⁺

  lemma₁ : ∀ n → cardAt n ≡ cardAt 0
  lemma₁ n = isConstCard n

  lemma₂Ext : ∀ n {idxₙ} {idx₀} (π : PathP (λ i → Idx (lemma₁ n i)) idxₙ idx₀)
    → level⁺ n .members idxₙ ≡ level⁺ n .members (idxAt idx₀ n)
  lemma₂Ext zero π = refl
  lemma₂Ext (suc n) {idxₙ} {idx₀} π =
    level⁺ (suc n) .members idxₙ ≡⟨ cong (level⁺ (suc n) .members) {!   !} ⟩
    level⁺ (suc n) .members
      (subst⁻ Idx (isConstCardSuc n)
       (idxAt idx₀ n)) ∎

  lemma₂ : ∀ n →
    PathP (λ i → Idx (lemma₁ n i) → UnordedTree n)
      (level⁺ n .members)
      (λ idx₀ → level⁺ n .members (idxAt idx₀ n))
  lemma₂ n = funExtDep (lemma₂Ext n) -- (λ {x₀ = idxₙ} {x₁ = idx₀} p → cong (level⁺ n .snd) {! idx₀Path tree⁺ idx₀ n  !})

  elemPath : ∀ n → α (α⁻¹ tree⁺) .elements n ≡ tree⁺ .elements n
  elemPath n =
    α (α⁻¹ tree⁺) .elements n ≡⟨⟩
    map (λ tree → tree .level n) (α⁻¹ tree⁺) ≡⟨⟩
    ⟅ idx₀ ↦ zippedTrees idx₀ n ⟆ ≡⟨⟩
    ⟅ idx₀ ↦ treesAt n (idxAt idx₀ n) ⟆ ≡⟨⟩
    ⟅ idx₀ ↦ level⁺ n .members (idxAt idx₀ n) ⟆ ≡⟨ sym (BagPathP (lemma₁ n) (lemma₂ n)) ⟩
    level⁺ n ≡⟨⟩
    tree⁺ .elements n ∎

α⁻¹∘α : (trees : Bag ωTree) → α⁻¹ (α trees) ≡ trees
α⁻¹∘α trees@(⟅ branches ⟆) = BagPath branchesPath where
  open Limit.ChainLimit

  open Zip

  -- TODO: This should follow from idx₀Path
  idxPath′ : ∀ (n : ℕ) (ix : Idx (cardAt (α trees) n)) → idxAt (α trees) ix n ≡ ix
  idxPath′ zero ix = refl
  idxPath′ (suc n) ix = idxPath (α trees) ix n ∙ idxPath′ n ix

  elementsExt : ∀ idx' n → zippedTree (α trees) idx' .elements n ≡ branches idx' .elements n
  elementsExt idx' n = cong (λ ix → branches ix .elements n) (idxPath′ n idx')

  isChainLimitPath : ∀ idx₀ n →
    PathP (λ i → !^ n (elementsExt idx₀ (suc n) i) ≡ elementsExt idx₀ n i)
      (isChainLimitZippedTrees (α trees) idx₀ n)
      _
  isChainLimitPath idx₀ n = compPathP' {!   !} {!   !}

  branchesPathExt : ∀ idx' → (α⁻¹ (α trees)) .members idx' ≡ branches idx'
  branchesPathExt idx' = ωTreePathP (elementsExt idx') (isChainLimitPath idx')

  _ : (α⁻¹ (α trees)) .members ≡ zippedTree (α trees)
  _ = refl

  branchesPath : (α⁻¹ (α trees)) .members ≡ branches
  branchesPath = funExt branchesPathExt

open Iso

αIso : Iso (Bag ωTree) ωBagOfTrees
αIso .fun = α
αIso .inv = α⁻¹
αIso .rightInv = α∘α⁻¹
αIso .leftInv = α⁻¹∘α

isLimitPreservingBag : BagChain.isLimitPreserving
isLimitPreservingBag = isoToEquiv αIso
