{-# OPTIONS --safe #-}

{-
Prerequisites
-------------

This library has been tested with the following software versions:
 * Agda v2.6.2.2
 * The Cubical library, version 0.4 (23th Nov 2022):
     https://github.com/agda/cubical/releases/tag/v0.4

Type checking the code
----------------------

Type check the code by running Agda in Safe Mode:

    $ agda --safe ./README.agda

Alternatively, use the provided Nix flake (see file `flake.nix`) to reproducibly
type check the library with all dependencies pinned to working versions:

    $ nix build

A development shell that includes all of the dependencies can be spawned via

    $ nix shell
    (nix-shell) $ which agda
    /nix/store/dfr3d08mx77isqzkgxnm0vr2rrfpc20x-agdaWithPackages-2.6.2.2/bin/agda
    (nix-shell) $ agda --safe ./README.agda
    ...
-}

module README where

open import Multiset.Prelude
open import Multiset.Util using (isInjective)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism using (Iso ; section)
open import Cubical.Data.List as List using (List)
open import Cubical.Data.Nat as Nat using (ℕ ; suc)
open import Cubical.Data.SumFin using (Fin)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)

-- open import Cubical.Foundations.Equiv
-- open import Cubical.Data.FinSet using (FinSet)
-- open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

-- 3. The Finite Bag Functor in Sets
-- ---------------------------------

-- 3.1 The free commutative monoid
-- -------------------------------

import Multiset.FCM

-- Finite multisets, defined as the free commutative monoid on a type.
-- Implemented as a HIT:
FCM : ∀ {ℓ} → Type ℓ → Type ℓ
FCM = Multiset.FCM.M

-- 3.2 As a Quotient of Lists
-- --------------------------

import Multiset.Ordering.Order
import Multiset.Ordering.PermEquiv

-- Inductive definition of permutations of lists:
Perm : ∀ {A} → List A → List A → Type
Perm = Multiset.Ordering.Order.Perm

-- Finite multisets as lists modulo permutation:
List[_]/Perm : Type → Type
List[_]/Perm = Multiset.Ordering.Order.Mset

import Multiset.ListQuotient.Base

-- Relational lifting of R to a relation on lists
DRelator : ∀ {ℓ} {X Y : Type ℓ} (R : X → Y → Type ℓ) → List X → List Y → Type ℓ
DRelator = Multiset.ListQuotient.Base.DRelator

Relator : ∀ {ℓ} {X : Type ℓ} (R : X → X → Type ℓ) → List X → List X → Type ℓ
Relator = Multiset.ListQuotient.Base.Relator

import Multiset.Ordering.PermEquiv

-- The relational lifting of paths witnesses exactly the mere existence of a permutation:
∥Perm∥₁≃Relator≡ : {A : Type} {xs ys : List A} → ∥ Perm xs ys ∥₁ ≃ Relator _≡_ xs ys
∥Perm∥₁≃Relator≡ = Multiset.Ordering.PermEquiv.∥Perm∥₁≃Relator=


-- 3.3 As an Analytic Functor
-- --------------------------

import Multiset.FMSet
import Multiset.ListQuotient.FMSetEquiv

-- Finite multisets as an analytic functor:
FMSet : ∀ {ℓ} → Type ℓ → Type ℓ
FMSet = Multiset.FMSet.FMSet

-- The action of the symmetric group that `FMSet` is quotiented by:
SymAct : ∀ {X} → (n : ℕ) → (v w : Fin n → X) → Type
SymAct = Multiset.FMSet.SymmetricAction

-- The non-propositionally truncated version:
SymAct∞ : ∀ {X} → (n : ℕ) → (v w : Fin n → X) → Type
SymAct∞ = Multiset.ListQuotient.FMSetEquiv.SymmetricActionΣ

-- Abbreviation with size implict:
_∼_ = Multiset.FMSet._∼_

-- Finite choice for Fin-indexed types:
import Multiset.FiniteChoice

module _ {n : ℕ} (Y : Fin n → Type) where
  finChoiceEquiv : ((k : Fin n) → ∥ Y k ∥₂) ≃ ∥ ((k : Fin n) → Y k) ∥₂
  finChoiceEquiv = Multiset.FiniteChoice.setFinChoice≃ Y

  box : ((k : Fin n) → ∥ Y k ∥₂) → ∥ ((k : Fin n) → Y k) ∥₂
  box = Multiset.FiniteChoice.box

  unbox : ∥ ((k : Fin n) → Y k) ∥₂ → ((k : Fin n) → ∥ Y k ∥₂)
  unbox = Multiset.FiniteChoice.unbox

-- Dependent eliminator for Fin-indexed families:
elim-∥_∥₂-fin : {n : ℕ} (X : Type) {B : (Fin n → ∥ X ∥₂) → Type}
  → ((∣v∣ : Fin n → ∥ X ∥₂) → isSet (B ∣v∣))
  → ((v : Fin n → X) → B (∣_∣₂ ∘ v))
  → (v : Fin n → ∥ X ∥₂) → B v
elim-∥ X ∥₂-fin = Multiset.FiniteChoice.elimₙ

-- Propositional computation rule for the eliminator:
elim-∥_∥₂-finᵝ : {n : ℕ} (X : Type) {B : (Fin n → ∥ X ∥₂) → Type}
  → (setB : (∣v∣ : Fin n → ∥ X ∥₂) → isSet (B ∣v∣))
  → (choice : (v : Fin n → X) → B (∣_∣₂ ∘ v))
  → (v : Fin n → X)
  → elim-∥ X ∥₂-fin setB choice (∣_∣₂ ∘ v) ≡ choice v
elim-∥ X ∥₂-finᵝ = Multiset.FiniteChoice.elimₙ-comp

import Multiset.FMSet.Properties using (module STInvariance)

-- FMSet is invariant under set truncation:
FMSetTruncInvariance : {X : Type} → FMSet ∥ X ∥₂ ≃ FMSet X
FMSetTruncInvariance = Multiset.FMSet.Properties.STInvariance.STInvarianceEquiv

-- 3.4 Equivalence of Presentations
-- --------------------------------

import Multiset.Equivalences.FCM-PList
import Multiset.Equivalences.PList-RelatorList

-- The four presentations of finite multisets above are provably equivalent:
FMSetEquivs : ∀ X → FCM X ≃ FMSet X
FMSetEquivs X =
  FCM X                ≃⟨ Multiset.Equivalences.FCM-PList.M≃PList ⟩
  List X / Perm        ≃⟨ Multiset.Equivalences.PList-RelatorList.List/Perm≃List/Relator≡ ⟩
  List X / Relator _≡_ ≃⟨ invEquiv Multiset.ListQuotient.FMSetEquiv.FMSet≃List/Relator= ⟩
  FMSet X ■

-- All equivalences above are natural:
FCM≃List/Perm-natural = Multiset.Equivalences.FCM-PList.PListToM-nat
List/Perm≃List/Relator-natural = Multiset.Equivalences.PList-RelatorList.List/Perm→List/Relator≡-nat
FMSet→List/Relator=-natural = Multiset.Equivalences.PList-RelatorList.FMSet→List/Relator=-nat


-- Variations
-- ----------

-- The following are not mentioned explicitly in the paper, but are used when convenient:
import Multiset.Util.BundledVec
import Multiset.ListQuotient.ListFinality

-- A variation of lists, as a vector bundled with its length.
List' : Type → Type
List' = Multiset.Util.BundledVec.ΣVec

-- This type is convenient when proving that List preserves ω-chain limits,
-- since that relies on access to a countable family of lists *of the same length*.
_ = Multiset.ListQuotient.ListFinality.isTerminalFix⁻

-- The relational lifting, but for lists bundled with a length:
Relator' : _
Relator' = Multiset.Util.BundledVec.Relator
  
-- The two definitions are naturally equivalent:
ΣVec-List-nat = Multiset.ListQuotient.ListFinality.ΣVec-List-EquivNat

-- Equivalences of FCM and a HIT of head-permuted lists, defined in Cubical.HITs.FiniteMultiset.
open import Cubical.HITs.FiniteMultiset.Base using () renaming (FMSet to HeadPList)
import Multiset.Equivalences.FCM-HeadPList

_ : ∀ {X : Type} → FCM X ≃ HeadPList X
_ = Multiset.Equivalences.FCM-HeadPList.M≃HeadPList

-- 3.5 Definable Quotients and Sorting

import Multiset.Ordering.Order

isLinOrder : {A : Type} (R : A → A → Type) → Type
isLinOrder = Multiset.Ordering.Order.isLinOrder

module _ {A : Type} (setA : isSet A) (R : A → A → Type) (linR : isLinOrder R) where
  import Multiset.Ordering.FMSetOrder
  module S = Multiset.Ordering.FMSetOrder.SortingFMSet setA R linR

  -- For linearly ordered A, `∼` induces a definable quotient:
  sort : (n : ℕ) → (Fin n → A) / _∼_ → (Fin n → A)
  sort = S.sortPVect

  SymActDefineable : (n : ℕ) → section SQ.[_] (sort n)
  SymActDefineable = S.sortPVect-section

  -- For linearly ordered A, there is a canonical permutation between
  -- any two unordered finite sets of A's:
  SymActUntruncate : (n : ℕ) (v w : Fin n → A) → SymAct n v w → SymAct∞ n v w
  SymActUntruncate = S.canonicalS

  -- This defines a linear order on finite multisets:
  LexFMSet : FMSet A → FMSet A → Type
  LexFMSet = S.LexFMSet

  linLexFMSet : isLinOrder LexFMSet
  linLexFMSet = S.linLexFMSet

-- 4 The Final Coalgebra in Sets
-- -----------------------------

import Multiset.Functor
import Multiset.Coalgebra

-- The structure of a functor of types:
Functor : (F : Type → Type) → Type _
Functor = Multiset.Functor.Functor

-- Coalgebras are unbundled functions:
Coalgebra : (F : Type → Type) → ⦃ Functor F ⦄ → _
Coalgebra F = ∀ {A} → A → F A

-- Coalgebra morphisms:
CoalgebraMorphism : (F : Type → Type) → ⦃ Functor F ⦄ → ∀ {A B} → (α : A → F A) → (β : B → F B) → Type _
CoalgebraMorphism = Multiset.Coalgebra.CoalgebraMorphism


-- 4.1 As an ω-Limit
-- -----------------

-- Definition of the terminal ω-chain of an endofunctor:
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( ch        -- The chain 1 ← F(1) ← F²(1) ← ...
    ; _^_       -- Helper for the type Fⁿ(1)
    ; _map-!^_  -- Helper for the iterated map !ⁿ : Fⁿ⁺¹(1) → Fⁿ(1)
    ; Lim       -- The type of limits of such a chain
    ; ShLim     -- The limits of the shifted chain F(1) ← F²(1) ← F³(1) ← ...
    ; isLimitPreserving
    )

module _ (F : Type → Type) {{FunctorF : Functor F}} where

  -- The limit and the shifted limit of a chain are equivalent
  shift : Lim F ≃ ShLim F
  shift = invEquiv (TerminalChain.ShLim≃Lim F)

  -- The family of projections out of a limit.
  ℓ : (n : ℕ) → Lim F → F ^ n
  ℓ = TerminalChain.cut F
  -- NB: This is not called "ℓ" in the rest of the code because
  -- of naming conflicts with universe levels.

  -- The limit-preservation maps into the shifted limit.
  pres : F (Lim F) → ShLim F
  pres = TerminalChain.pres F

  -- If F preserves limits of this shape, it admits a fixpoint:
  fix : isLimitPreserving F → F (Lim F) ≃ Lim F
  fix = TerminalChain.fix

  -- The inverse of the above equivalence is the structure map
  -- of the final coalgebra:
  coalg : isLimitPreserving F → Lim F → F (Lim F)
  coalg = TerminalChain.Fixpoint.fix⁻

import Multiset.FCM.Limit

-- The Lesser Limit Principle of Omniscience:
open import Multiset.Omniscience using (LLPO)

-- Injectivity of the limit-preservation map of finite multisets implies LLPO.
-- Note that this is proved for the presentation as a HIT:
InjectiveFMSetPresToLLPO : isInjective (pres FCM) → LLPO
InjectiveFMSetPresToLLPO = Multiset.FCM.Limit.pres-inj⇒llpo

-- The crucial lemma that the above proof depends on:
FMSetAlternationLemma = Multiset.FCM.Limit.diag-ysᶜ-islim-alternating

import Multiset.ListQuotient.ToInjectivity

-- LLPO also implies the injectivity of the limit-preservation map.
-- This time, we use lists modulo a relational lifting for the proof:
LLPOToInjectiveFMSetPres : LLPO → isInjective (pres (λ X → List X / Relator _≡_))
LLPOToInjectiveFMSetPres = Multiset.ListQuotient.ToInjectivity.llpo⇒pres-inj

import Multiset.FMSet.Limit

-- Using the third preservation of finite multisets in terms of an analytic
-- functor, we can at least show that the limit-preservation map has a section,
-- i.e. the limit is weakly preserved:
LexFMSet^ : (n : ℕ) → FMSet ^ n → FMSet ^ n → Type
LexFMSet^ = Multiset.FMSet.Limit.LexFMSet^

linLexIterFMSet : ∀ n → isLinOrder (LexFMSet^ n)
linLexIterFMSet = Multiset.FMSet.Limit.linLexFMSet^

FMSetPresSection : section (pres FMSet) Multiset.FMSet.Limit.PresSection.pres⁻¹
FMSetPresSection = Multiset.FMSet.Limit.PresSection.pres-section

-- 4.2 As a Quotient of the Final List-Coalgebra
-- ---------------------------------------------

import Multiset.ListQuotient.Bisimilarity

-- List has a final coalgebra whose carrier is the type of ordered non-wellfounded trees:
Tree = Multiset.ListQuotient.ListFinality.Tree

_ : Tree ≡ Lim List'
_ = refl

coalgList : Tree → List' Tree
coalgList = Multiset.ListQuotient.ListFinality.fix⁻

-- Relation on finite approximation of infinite trees that relates
-- them up to the order of their subtrees:
Approx : (n : ℕ) → List' ^ n → List' ^ n → Type
Approx = Multiset.ListQuotient.Bisimilarity.Approx

!-Approx : (n : ℕ) {s t : (List' ^ (suc n))}
  → Relator' (Approx n) s t → Approx n ((List' map-!^ n) s) ((List' map-!^ n) t)
!-Approx = Multiset.ListQuotient.Bisimilarity.Approx-π

-- Bisimilarity of trees.  This is the limit of a chain defined in
-- terms of `Approx` above:
Bisim : (s t : Tree) → Type
Bisim = Multiset.ListQuotient.Bisimilarity.Bisim

open import Multiset.Axioms.Choice as AOC using (AC)
import Multiset.ListQuotient.LLPO

open import Cubical.Categories.Functor using () renaming (Functor to Functor')
import Multiset.Categories.Coalgebra as Cat
open import Cubical.Categories.Instances.Sets using (SET)

-- Under the assuming that `coalgList` is a morphism of setoids, we can deduce the following:
module _ (isSetoidMorCoalgList : (∀ {s} {t} → Bisim s t → Relator' Bisim (coalgList s) (coalgList t))) where

  -- 1) The anti-constructive principle LLPO:
  isSetoidMorphismCoalgListToLLPO : LLPO
  isSetoidMorphismCoalgListToLLPO = Multiset.ListQuotient.LLPO.fix⁻-preserves-≈→LLPO isSetoidMorCoalgList

  import Multiset.Setoid.Category
  open import Cubical.Categories.Category using (Category)

  -- The category of setoids: Objects are pairs of hSets and prop-valued equivalence relations;
  -- morphisms are relation-preserving functions modulo the relation in the domain
  SetoidCategory : Category (ℓ-suc ℓ-zero) ℓ-zero
  SetoidCategory = Multiset.Setoid.Category.SetoidCategory ℓ-zero ℓ-zero

  FMSetoid : Functor' SetoidCategory SetoidCategory
  FMSetoid = Multiset.Util.BundledVec.RelatorFunctor

  import Multiset.ListQuotient.Finality

  -- 2) coalgList induces a terminal coalgebra of the functor `FMSetoid : (X, R) ↦ (List' X, Relator R)`:
  finalFMSetoidCoalgebra : Cat.TerminalCoalgebra FMSetoid
  finalFMSetoidCoalgebra = Multiset.ListQuotient.Finality.finalFMSetoidCoalgebra isSetoidMorCoalgList

  import Multiset.ListQuotient.Fixpoint

  FMSet' : Type → Type
  FMSet' X = List' X / (Relator' _≡_)

  -- 3) coalgList lifts to a FMSet-coalgebra, and induces a fixpoint of trees modulo bisimilarity:
  coalgFMSet : Tree / Bisim → FMSet' (Tree / Bisim)
  coalgFMSet = Multiset.ListQuotient.Fixpoint.fixQ⁻ isSetoidMorCoalgList

  FMSetFixpointTree/Bisim : FMSet' (Tree / Bisim) ≃ Tree / Bisim
  FMSetFixpointTree/Bisim = Multiset.ListQuotient.Fixpoint.FMSetFixpointTree/Bisim isSetoidMorCoalgList

  FMSetFunctor : Functor' (SET _) (SET _)
  FMSetFunctor = Multiset.ListQuotient.Fixpoint.FMSetFunctor

  -- 4) Assuming the axiom of choice this fixpoint is the largest, i.e. coalgFMSet is the final coalgebra:
  FinalFMSetCoalgebra : AC _ _ _ → Cat.TerminalCoalgebra FMSetFunctor
  FinalFMSetCoalgebra = Multiset.ListQuotient.Fixpoint.TerminalfixQ⁻ isSetoidMorCoalgList


-- 5 The Finite Bag Functor in Groupoids
-- -------------------------------------

open import Cubical.Data.FinSet.Base using (FinSet)
import Multiset.Tote

-- The "large" type of bags, defined in terms of FinSet:
Tote : Type₀ → Type₁
Tote = Multiset.Tote.Tote

isGroupoidTote : ∀ {X : Type} → isGroupoid X → isGroupoid (Tote X)
isGroupoidTote = Multiset.Tote.isGroupoidTote

-- The set-truncation of this type is naturally equivalent to finite multisets:
FMSetToteTruncEquiv : {X : Type} → FMSet X ≃ ∥ Tote X ∥₂
FMSetToteTruncEquiv = Multiset.Tote.FMSet≃∥Tote∥₂

FMSet→∥Tote∥₂ : ∀ {X : Type} → FMSet X → ∥ Tote X ∥₂
FMSet→∥Tote∥₂ = equivFun FMSetToteTruncEquiv

isNatural-FMSetToteTruncEquiv : ∀ {X Y : Type} (f : X → Y)
  → FMSet→∥Tote∥₂ ∘ Multiset.FMSet.map f ≡ ST.map (Multiset.Tote.map f) ∘ FMSet→∥Tote∥₂
isNatural-FMSetToteTruncEquiv = Multiset.Tote.isNatural-FMSet≃∥Tote∥₂

import Multiset.Bij

-- A small type, equivalent to the large type of (Bishop-) finite types:
Bij : Type
Bij = Multiset.Bij.Bij

BinFinSetEquiv : Bij ≃ FinSet ℓ-zero
BinFinSetEquiv = Multiset.Bij.Bij≃FinSet

import Multiset.Bag

Bag : Type → Type
Bag = Multiset.Bag.Bag

-- Both defintions, small and large, are equivalent:
BagToteEquiv : ∀ {X : Type} → Bag X ≃ Tote X
BagToteEquiv = Multiset.Bag.Bag≃Tote

-- [NOTE 1]: The equivalence is easily seen to be natural,
-- but Agda gets stuck when proving this, since it
-- seems to try and expand the definition of `Multiset.Bij.Bij→FinSet`:

abstract
  _ : Bij → FinSet ℓ-zero
  _ = Multiset.Bij.Bij→FinSet

-- 6 The Final Coalgebra in Groupoids
-- ----------------------------------

-- Bag preserves limits of ω-chains, so by [Ahrens et al. '15] it admits a final coalgebra:
isLimitPreservingBag : isEquiv (pres Bag)
isLimitPreservingBag = Multiset.Bag.isLimitPreservingBag

import Multiset.FMSet.Fixpoint

-- Truncating the type of Bag-limits yields a fixpoint for FMSet:
FMSetFixpointTruncBagLim : FMSet ∥ Lim Bag ∥₂ ≃ ∥ Lim Bag ∥₂
FMSetFixpointTruncBagLim = Multiset.FMSet.Fixpoint.FMSetFixSetTruncTree

import Multiset.FMSet.Finality

FMSetFunctor' : Functor' (SET _) (SET _)
FMSetFunctor' = Multiset.FMSet.Finality.FMSetFunctor

module _
  -- Assume bag has a final coalgebra (follows from `isLimitPreservingBag` + [Ahrens et al. '15])
  (ana : {X : Type} → (c : X → Bag X) → X → Lim Bag)
  (anaEq : {X : Type} (c : X → Bag X)
    → ana c ≡ Multiset.Bag.fix⁺ ∘ Multiset.Bag.map (ana c) ∘ c)
  (anaUniq : {X : Type} (c : X → Bag X)
    → (h : X → Lim Bag)
    → h ≡ Multiset.Bag.fix⁺ ∘ (Multiset.Bag.map h) ∘ c
    → ana c ≡ h)
  -- The equivalence ∥ Bag Y ∥₂ ≃ FMSet Y is natural.
  -- See [NOTE 1] above why this is necessary:
  (e : {Y : Type} → ∥ Bag Y ∥₂ ≃ FMSet Y)
  (eNat : ∀{Y Z} (f : Y → Z) → equivFun e ∘ ST.map (Multiset.Bag.map f) ≡ Multiset.FMSet.map f ∘ equivFun e)
  where
  
  -- Assuming two instance of choice, one for groupoids and one for sets, FMSet admits a final coalgebra in the category of hSets:
  FMSetFinalCoalgebra : (ac32 : AOC.AC[Gpd,Set] ℓ-zero ℓ-zero) → (ac : AOC.AC[Set,Prop] ℓ-zero ℓ-zero) → Cat.TerminalCoalgebra FMSetFunctor'
  FMSetFinalCoalgebra = Multiset.FMSet.Finality.FinalityWithChoice.FMSetFinalCoalgebra ana anaEq anaUniq e eNat

  import Multiset.FMSet.FiniteFinality

  coalgFinite : Cat.Coalgebra FMSetFunctor'
  coalgFinite = Multiset.FMSet.FiniteFinality.FinalityFinite.coalg ana anaEq anaUniq e eNat

  -- When not assuming choice, there is still a unique coalgebra morphism from a coalgebra with finite carrier and `coalg'`:
  uniqueCoalgMorphismFinCarrier : ∀ n (c : Fin n → FMSet (Fin n)) → isContr (Cat.CoalgebraHom FMSetFunctor' (Cat.coalgebra c) coalgFinite)
  uniqueCoalgMorphismFinCarrier = Multiset.FMSet.FiniteFinality.FinalityFinite.uniqueFiniteCoalg ana anaEq anaUniq e eNat
