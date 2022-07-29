module Multiset.OverBij.Properties where

open import Multiset.OverBij.Base as OverBij
open import Multiset.Bij as Bij
open import Multiset.Chains
  using
    ( Chain
    ; Cochain
    ; module Limit
    ; module FunctorChain
    ; module Colimit
    )
open import Multiset.Util.Path
  using
    ( subst⁻-filler
    ; transport⁻Domain
    ; transportDomain
    ; [_∣_≡_]
    )
open import Multiset.Util.Square using (kiteFiller)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
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

open module BagChain = FunctorChain Bag (OverBij.map) Unit (! (Bag Unit))
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
    ( elements to depth
    ; isChainLimit to cut
    )

open Bag

BagUnit≃Bij : Bag Unit ≃ Bij
BagUnit≃Bij = isoToEquiv BagIsoΣ ∙ₑ Σ.Σ-contractSnd {B = λ (x : Bij) → Idx x → Unit} (λ _ → isContrΠUnit) where
  isContrΠUnit : {X : Type} → isContr (X → Unit)
  isContrΠUnit {X} = (! X) , λ f → refl

-- TODO: Look at Ahrens et al, use Lemma 11 to attempt Lemma 13.
-- * L^P : ωBagOfTrees
-- * P(L) : Bag (ωTree)

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
  bagAt n = map (λ tree → tree .depth n) trees

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

  isConstCard' : ∀ m n → cardAt m ≡ cardAt n
  isConstCard' m n = isConstCard m ∙ sym (isConstCard n)

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

  -- Cast an index into the nᵗʰ bag to an index into the (n+1)ˢᵗ bag.
  idxCastSuc : {n : ℕ} → Idx (cardAt n) → Idx (cardAt (suc n))
  idxCastSuc {n = n} = subst⁻ Idx (isConstCardSuc n)

  -- Same for casting 0ᵗʰ ↦ nᵗʰ.
  idx₀Cast : (n : ℕ) → Idx card₀ → Idx (cardAt n)
  idx₀Cast n = subst⁻ Idx (isConstCard n)
  -- idx₀Cast zero idx₀ = idx₀
  -- idx₀Cast (suc n) idx₀ = idxCastSuc (idx₀Cast n idx₀)

  idx₀CastPath : {n : ℕ} (idx₀ : Idx card₀)
    → PathP (λ i → Idx (isConstCard n i)) (idx₀Cast n idx₀) idx₀
  idx₀CastPath {n = n} idx₀ = symP (subst⁻-filler Idx (isConstCard n) idx₀)

  idxCastSucPath : {n : ℕ} (idx₀ : Idx card₀)
    → PathP (λ i → Idx (isConstCardSuc n i)) (idx₀Cast (suc n) idx₀) (idx₀Cast n idx₀)
  idxCastSucPath {n = n} idx₀ = compPathP' castToZero castFromZero where
    castToZero : _
    castToZero = idx₀CastPath {n = suc n} idx₀

    castFromZero : _
    castFromZero = symP (idx₀CastPath {n = n} idx₀)

  -- cutCohExt' : ∀ n (idx₀ : Idx card₀)
  --   → !^ n (treesAt (suc n) (idx₀Cast (suc n) idx₀)) ≡ treesAt n (idx₀Cast n idx₀)
  -- cutCohExt' n idx₀ = cutCohExt n _ _ (symP-fromGoal (subst⁻-filler Idx (isConstCardSuc n) (idx₀Cast n idx₀)))

  -- Casting between arbitrary indices:
  -- idxCast : {m n : ℕ} → Idx (cardAt m) → Idx (cardAt n)
  -- idxCast {m = m} {n = n} = subst Idx (isConstCard' m n)

  -- idxCast≡ : (m n : ℕ) → Idx (cardAt m) ≡ Idx (cardAt n)
  -- idxCast≡ m n = cong Idx (isConstCard' m n)

  -- Assuming we're given an index into the first bag, we can build
  -- a non-wellfounded tree from all the (wellfounded) trees at the
  -- corresponding indices up the chain of bags:
  module _ (idx₀ : Idx card₀) where

    -- All bags have the same cardinality, so convert idx₀ into an
    -- index into the nᵗʰ bag along the chain.
    idxAt : (n : ℕ) → Idx (cardAt n)
    idxAt n = idx₀Cast n idx₀

    -- Yes, these indices are indeed the same.
    -- TODO: Can we omit this and use `isConstCard` directly in the
    -- definitions below?
    idxPath : ∀ n → PathP (λ i → Idx (isConstCardSuc n i)) (idxAt (suc n)) (idxAt n)
    idxPath n = idxCastSucPath idx₀ -- symP (subst⁻-filler Idx (isConstCardSuc n) (idxAt n))

    -- We use idxAt to get a tree of depth n from the nᵗʰ bag:
    zippedTrees : (n : ℕ) → UnordedTree n
    zippedTrees n = treesAt n (idxAt n)

    -- TODO: Same as above, can we get rid of this and use isConstCard directly?
    idx₀Path : ∀ n → PathP (λ i → Idx (isConstCard n i)) (idxAt n) idx₀
    idx₀Path n = idx₀CastPath {n = n} idx₀

    -- This sequence of trees does indeed form a limit:
    isChainLimitZippedTrees : ∀ n → (!^ n) (zippedTrees (suc n)) ≡ zippedTrees n
    isChainLimitZippedTrees n = cutCohExt n (idxAt (suc n)) (idxAt n) (idxPath n)

    open Limit.ChainLimit

    zippedTree : ωTree
    zippedTree .elements = zippedTrees
    zippedTree .isChainLimit = isChainLimitZippedTrees

  reIndex : ∀ n
    → PathP (λ i → Idx (isConstCard n i) → UnordedTree n)
      (treesAt n)
      (λ idx₀ → treesAt n (idx₀Cast n idx₀))
  reIndex n = transport⁻Domain (treesAt n)

  zipped : Bag ωTree
  zipped = ⟅ zippedTree idx₀ ∣ idx₀ ∈ card₀ ⟆

α⁻¹ : ωBagOfTrees → (Bag ωTree)
α⁻¹ tree⁺ = Zip.zipped tree⁺

α∘α⁻¹ : ∀ tree⁺ → α (α⁻¹ tree⁺) ≡ tree⁺
α∘α⁻¹ tree⁺ = ω⁺TreePathP elemPath elemCoh where
  open Limit.ChainLimit renaming (elements to bag)

  open Zip tree⁺ using
    ( isConstCard
    ; zippedTrees
    ; reIndex
    )

  elemPath : ∀ n → α (α⁻¹ tree⁺) .bag n ≡ tree⁺ .bag n
  elemPath n =
    α (α⁻¹ tree⁺) .bag n ≡⟨⟩
    map (λ tree → tree .depth n) (α⁻¹ tree⁺) ≡⟨⟩
    ⟅ idx₀ ↦ zippedTrees idx₀ n ⟆ ≡⟨ sym (BagPathP (isConstCard n) (reIndex n)) ⟩
    tree⁺ .bag n ∎

  open Unzip (α⁻¹ tree⁺) using
    ( isChainLimitBags
    )

  elemCoh : ∀ n → PathP (λ i → map (!^ n) (elemPath (suc n) i) ≡ elemPath n i)
    (isChainLimitBags n)
    _
  elemCoh n = {!  !}


α⁻¹∘α : (trees : Bag ωTree) → α⁻¹ (α trees) ≡ trees
α⁻¹∘α trees = BagPathPExt refl {! branchesPath!} where
  open Limit.ChainLimit renaming
    (elements to tree ; isChainLimit to treeCoh)

  open module Zipα = Zip (α trees) using
    ( idx₀Cast
    ; idx₀CastPath
    ; isConstCard
    ; card₀
    ; cardAt
    ; zippedTree
    ; zippedTrees
    ; isChainLimitZippedTrees
    )

  -- TODO: This should follow from idx₀Path
  idxPath′ : ∀ (n : ℕ) (ix : Idx (cardAt n)) → idx₀Cast n ix ≡ ix
  idxPath′ n ix = {! !} -- idx₀CastPath {n = n} ix
  -- idxPath′ zero ix = refl
  -- idxPath′ (suc n) ix = idxPath (α trees) ix n ∙ idxPath′ n ix

  foo : (idx : Idx (trees .card)) (n : ℕ) → UnordedTree n
  foo idx n = trees .members idx .depth n

  elementsExtP : ∀ (n : ℕ)
    → PathP (λ i → Idx (isConstCard n i) → UnordedTree n)
        (λ idx → foo idx n)
        (λ idx → trees .members (idx₀Cast n idx) .depth n)
  elementsExtP n = transport⁻Domain {p = cong Idx (isConstCard n)} (λ idx → trees .members idx .depth n)

  elementsExtP' : ∀ (n : ℕ) (idx₀ : Idx card₀)
    → subst⁻ (λ idx → Idx idx → UnordedTree n) (isConstCard n) (λ idx → trees .members (idx₀Cast n idx) .depth n) idx₀ ≡ trees .members idx₀ .depth n
  elementsExtP' n idx₀ = goal where
    goal = funExt⁻ (fromPathP (symP-fromGoal (elementsExtP n))) idx₀

    _ = {! foo !}

  lemma : ∀ (idx : _) (n : ℕ) →
    subst⁻ (λ idx → Idx idx → UnordedTree n) (isConstCard n) (λ idx → foo (idx₀Cast n idx) n) idx
      ≡ _ -- foo idx n
  lemma idx n = {! substCommSlice _ (λ idx → Idx idx → UnordedTree n) _ (sym (isConstCard n))  !}

  elementsExt : ∀ idx n → zippedTree idx .tree n ≡ trees .members idx .depth n
  elementsExt idx n =
    zippedTree idx .tree n ≡⟨⟩
    -- map (λ tree → tree .depth n) trees .members (subst⁻ Idx (Zip.isConstCard (α trees) n) idx) ≡⟨⟩
    map (λ tree → tree .depth n) trees .members (idx₀Cast n idx) ≡⟨⟩
    trees .members (idx₀Cast n idx) .depth n ≡⟨ sym {! substCommSlice _ (λ idx → Idx idx → UnordedTree n) _ (sym (isConstCard n)) !} ⟩
    subst⁻ (λ idx → Idx idx → UnordedTree n) (isConstCard n) (λ idx → trees .members (idx₀Cast n idx) .depth n) idx
      ≡⟨ elementsExtP' n idx ⟩
    trees .members idx .depth n ∎
    -- {! transport⁻Domain (λ x → x .tree n) !}

    -- congP () {! !} -- (idxPath′ n idx')

  isChainLimitPath : ∀ idx₀ n →
    PathP (λ i → !^ n (elementsExt idx₀ (suc n) i) ≡ elementsExt idx₀ n i)
      (isChainLimitZippedTrees idx₀ n)
      _
  isChainLimitPath idx₀ n = compPathP' {!   !} {!   !}

  branchesPathExt : ∀ (idx : Idx Zipα.card₀) → Zipα.zippedTree idx ≡ trees .members idx
  branchesPathExt idx = ωTreePathP (elementsExt idx) {! !} -- ωTreePathP (elementsExt idx) (isChainLimitPath idx)

  _ : (α⁻¹ (α trees)) .members ≡ zippedTree
  _ = refl

  branchesPath : (α⁻¹ (α trees)) .members ≡ trees .members
  branchesPath = funExt branchesPathExt

open Iso

αIso : Iso (Bag ωTree) ωBagOfTrees
αIso .fun = α
αIso .inv = α⁻¹
αIso .rightInv = α∘α⁻¹
αIso .leftInv = α⁻¹∘α

isLimitPreservingBag : BagChain.isLimitPreserving
isLimitPreservingBag = isoToEquiv αIso

β : ωBagOfTrees → (Bag ωTree)
β = {! !}

module Equiv where
  open import Cubical.Reflection.StrictEquiv
   using (strictEquiv ; strictIsoToEquiv)

  open import Multiset.Util.Trace as Trace
    using (Trace ; step ; connect ; constTrace ; TraceIso ; start)
  
  TraceFirst-snd : Trace Bij → Type
  TraceFirst-snd cardAt =
    Σ[ vs ∈ ((n : ℕ) → Vect (UnordedTree n) (cardAt .step n)) ]
    ∀ (n : ℕ) →
      PathP (λ i → Vect (UnordedTree n) (cardAt .connect n i))
        (vs n)
        (!^ n ∘ vs (suc n))

  TraceFirst : Type
  TraceFirst = Σ (Trace Bij) TraceFirst-snd

  toTraceFirstIso : Iso ωBagOfTrees TraceFirst
  toTraceFirstIso = go where
    go : Iso _ _
    fun go (lim elements isChainLimit) = trace , vects , vects-coh where
      step' : ℕ → Bij
      step' n = elements n .card

      connect' : ∀ n → step' n ≡ step' (suc n)
      connect' n = cong card (sym (isChainLimit n))

      trace : Trace Bij
      trace = step' , connect'

      vects : (n : ℕ) → Vect (UnordedTree n) (step' n)
      vects n = elements n .members

      vects-coh : ∀ n → PathP (λ i → Vect (UnordedTree n) (connect' n i)) (vects n) (λ idx → !^ n (vects (suc n) idx))
      vects-coh n = cong members (sym (isChainLimit n))
    inv go (trace , vects , vects-coh) = lim elements' isChainLimit' where
      elements' : (n : ℕ) → Bag (UnordedTree n)
      elements' n = ⟅ vects n idx ∣ idx ∈ trace .step n ⟆

      isChainLimit' : ∀ n → map (!^ n) (elements' (suc n)) ≡ elements' n
      isChainLimit' n = BagPathP (sym (trace .connect n)) (symP (vects-coh n))
    rightInv go (trace , vects , vects-coh) = ΣPathP (refl , ΣPathP (refl {x = vects} , refl {x = vects-coh}))
    leftInv go _ = {! !}

  OneCard-snd : (card : Bij) → Type
  OneCard-snd card =
    Σ[ vects ∈ ((n : ℕ) → Vect (UnordedTree n) card) ]
      ∀ (n : ℕ) →
        [ Vect (UnordedTree n) card
        ∣ (!^ n ∘ vects (suc n)) ≡ (vects n)
        ]

  OneCard : Type
  OneCard = Σ[ card ∈ Bij ] (OneCard-snd card)

  iso₆′ : (card₀ : Bij) → Iso (TraceFirst-snd (constTrace card₀)) (OneCard-snd card₀)
  iso₆′ card₀ = go where
    go : Iso _ _
    go .fun (vects , vects-coh) = vects , λ n → sym (vects-coh n)
    go .inv (vects , vects-coh) = vects , λ n → sym (vects-coh n)
    go .rightInv _ = refl
    go .leftInv _ = refl

  iso₅′ : Iso (Σ Bij (TraceFirst-snd ∘ constTrace)) TraceFirst
  iso₅′ = Σ.Σ-cong-iso-fst
    {A = Bij} {A' = Trace Bij} {B = TraceFirst-snd}
    (invIso TraceIso)

  iso₇′ : Iso (Σ Bij (TraceFirst-snd ∘ constTrace)) OneCard
  iso₇′ = Σ.Σ-cong-iso-snd
    {A = Bij}
    {B = TraceFirst-snd ∘ constTrace}
    {B' = OneCard-snd}
    iso₆′

  iso₈′ : Iso TraceFirst OneCard
  iso₈′ = compIso (invIso iso₅′) iso₇′

  -- TODO: Show that OneCard ≅ (Bag ωTree)
