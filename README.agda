{-# OPTIONS --safe #-}

-- Prerequisites
-- -------------
--
-- This library has been tested with the following software versions:
--  * Agda v2.6.2.2
--  * The Cubical library, version 0.4 (23th Nov 2022):
--      https://github.com/agda/cubical/releases/tag/v0.4
--
-- Type checking the code
-- ----------------------
--
-- Type check the code by running Agda in Safe Mode:
--
-- $ agda --safe ./README.agda
--
-- The modules Multiset.Coinductive.* require the Agda extension of Sized Types.
-- This is incompatible with Safe Mode, so check them like so:
--
-- $ agda --sized-types ./Multiset/Coinductive.agda
--
-- Alternatively, use the provided Nix flake (see file flake.nix) to reproducibly
-- type check the library with all dependencies pinned to working versions:
--
-- $ nix build
--
-- A development shell that includes all of the dependencies can be spawned via
--
-- $ nix shell
-- (nix-shell) which agda
-- /nix/store/dfr3d08mx77isqzkgxnm0vr2rrfpc20x-agdaWithPackages-2.6.2.2/bin/agda
-- (nix-shell) $ agda --safe ./README.agda
-- ...

module README where

open import Multiset.Prelude

open import Cubical.Foundations.Isomorphism using (Iso ; section)
open import Cubical.Foundations.Equiv
open import Cubical.Data.FinSet using (FinSet)
open import Cubical.Data.SumFin using (Fin)
open import Cubical.Data.Nat as Nat using (ℕ)
open import Cubical.Data.List as List using (List)
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂)

-- 3. The Finite Bag Functor in Sets

-- 3.1 The free commutative monoid

-- Definition as a HIT
open import Multiset.FCM as FCM
  renaming
    (M to FCM)

-- 3.2 As a Quotient of Lists

-- Lists modulo permutations
open import Multiset.Ordering.Order
  using (Perm)
  renaming (Mset to List[_]/Perm)
import Multiset.Ordering.PermEquiv

-- Equivalences of FCM and lists module permutations.
open import Multiset.Equivalences.FCM-PList
  using ()
  renaming (M≃PList to FCM≃List/Perm)

_ : ∀ {X} → FCM X ≃ List[ X ]/Perm
_ = FCM≃List/Perm

-- Equivalences of FCM and a HIT of head-permuted lists,
-- defined in Cubical.HITs.FiniteMultiset.
open import Cubical.HITs.FiniteMultiset.Base using () renaming (FMSet to HeadPList)
open import Multiset.Equivalences.FCM-HeadPList
  using ()
  renaming (M≃HeadPList to FCM≃HeadPList)

_ : ∀ {X : Type} → FCM X ≃ HeadPList X
_ = FCM≃HeadPList

-- Relational lifting
open import Multiset.ListQuotient.Base
  using (DRelator ; Relator)
import Multiset.ListQuotient.FMSetEquiv

-- Equivalence of lists modulo permutation and
-- lists modulo the relational lifting of equality.
open import Multiset.Equivalences.PList-RelatorList
  using (List/Perm≃List/Relator≡)

_ : ∀ {X} → List[ X ]/Perm ≃ (List X SQ./ Relator _≡_)
_ = List/Perm≃List/Relator≡

-- 3.3 As an Analytic Functor

open import Multiset.FMSet.Base as FMSet
  using (_∼_ ; FMSet ; PVect)
  renaming (SymmetricAction to SymAct)

open import Multiset.ListQuotient.FMSetEquiv
  using (FMSet≃List/Relator=)
  renaming (SymmetricActionΣ to SymAct')

_ : ∀ {X} → FMSet X ≃ List X SQ./ Relator _≡_
_ = FMSet≃List/Relator=

-- The four presentations of finite multisets
-- are provably equivalent:
_ : ∀ X → FCM X ≃ FMSet X
_ = λ X →
  FCM X                   ≃⟨ FCM≃List/Perm ⟩
  List[ X ]/Perm          ≃⟨ List/Perm≃List/Relator≡ ⟩
  List X SQ./ Relator _≡_ ≃⟨ invEquiv FMSet≃List/Relator= ⟩
  FMSet X ■

open import Multiset.FiniteChoice
  using
    (box ; unbox ; setFinChoice≃
    ; elimₙ ; elimₙ-comp
    )

-- The equivalence built from `box`:
Lemma1 : ∀ {n} {ℓ} (Y : Fin n → Type ℓ)
  → ((n₁ : Fin n) → ∥ Y n₁ ∥₂) ≃ ∥ ((k : Fin n) → Y k) ∥₂
Lemma1 = setFinChoice≃

-- The finite choice principle obtained from Lemma 1:
elim∥_∥₂-fin = elimₙ
elim∥_∥₂-finᵝ = elimₙ-comp

-- Theorem 1: FMSet is invariant under set truncation.
import Multiset.FMSet.Properties using (module STInvariance)
open Multiset.FMSet.Properties.STInvariance
  renaming (STInvarianceEquiv to FMSet∥-∥₂≃FMSet)

Theorem1 : ∀ {ℓ} {X : Type ℓ} → FMSet ∥ X ∥₂ ≃ FMSet X
Theorem1 = FMSet∥-∥₂≃FMSet

-- 3.4 Definable Quotients and Sorting
open import Multiset.Ordering.Order
  using
    ( isLinOrder -- Definition of a linear order
    )
open import Multiset.Ordering.FMSetOrder
  using (module SortingFMSet)

module _ {A : Type} (setA : isSet A) (R : A → A → Type) (linR : isLinOrder R) where
  module S = SortingFMSet setA R linR

  -- Extracting a vector from a finite multiset by sorting:
  sortFMSet : FMSet A → Σ[ n ∈ ℕ ] (Fin n → A)
  sortFMSet = S.sortFMSet

  -- Sorting members of a multisets (vectors up to permutation) is derived from the above:
  sortPVect : ∀ n → PVect A n → (Fin n → A)
  sortPVect = S.sortPVect

  -- Sorting is a section of the set quotient constructor
  Proposition1 : ∀ n → section SQ.[_] (sortPVect n)
  Proposition1 = S.sortPVect-section

  -- For linearly ordered A, the propositional truncation of SymAct can be removed.
  Proposition2 : ∀ n (v w : Fin n → A)
    → SymAct n v w
    → SymAct' n v w
  Proposition2 = S.canonicalS

-- 4 The Final Coalgebra in Sets

-- 4.1 As an ω-Limit
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor -- A "functor" on types
    ; ch -- The chain 1 ← F(1) ← F²(1) ← ...
    ; Lim -- The type of limits of such a chain
    ; ShLim -- The limits of the shifted chain F(1) ← F²(1) ← F³(1) ← ...
    ; pres -- The limit-preservation map
    ; isLimitPreserving
    )
module _ (F : Type → Type) {{FunctorF : Functor F}} where

  -- The limit-preservation maps into the shifted limit.
  _ : F (Lim F) → ShLim F
  _ = pres F

  -- If F preserves limits of this shape, it admits a fixpoint:
  _ : isLimitPreserving F → F (Lim F) ≃ Lim F
  _ = TerminalChain.fix

open import Multiset.FCM.Limit
  using
    ( diag-ysᶜ-islim-alternating
    ; pres-inj⇒complete
    )

Lemma2 = diag-ysᶜ-islim-alternating

-- Injectivity of pres implies LLPO.
-- We prove completeness, which implies LLPO.
Theorem2 = pres-inj⇒complete

open import Multiset.ListQuotient.ToInjectivity
  using (llpo⇒pres-inj)

-- Using the equivalent type (List X / Perm), we can show that
-- LLPO implies the injectivity of the limit-preservation map.
Theorem3 = llpo⇒pres-inj

open import Multiset.FMSet.Base using (FMSet)
open import Multiset.FMSet.Limit using (module SplitEpimorphism)

-- The limit preservation map is a split epimorphism.
Theorem4 : section (pres FMSet) (SplitEpimorphism.pres⁻¹)
Theorem4 = SplitEpimorphism.pres-section

-- 4.2 As a Quotient of the Final List-Coalgebra

-- See the module Multiset.Coinductive for the results of this section.
-- They aren't included here since they are defined using Agda's sized types,
-- which are enabled with the --sized-types flag.

-- 5 The Finite Bag Functor in Groupoids

open import Multiset.Tote
  using
    ( Tote -- The type of large bags.
    ; FMSet≃∥Tote∥₂
    ; isGroupoidTote
    )

-- Note that the universe level goes up by one:
_ : Type → Type₁
_ = Tote

Proposition4 : {X : Type} → isGroupoid X → isGroupoid (Tote X)
Proposition4 = isGroupoidTote

-- The definition in groupoids, when truncated yields the definition in sets:
Theorem8 = FMSet≃∥Tote∥₂

-- The small axiomatization of FinSet:
open import Multiset.Bij.Base using (Bij)
open import Multiset.Bij.Properties using (Bij≃FinSet ; Bij→FinSet)

Proposition5 : Bij ≃ FinSet _
Proposition5 = Bij≃FinSet

-- ...and the improved Bag-functor:
open import Multiset.Bag
  using
    ( Bag
    ; BagLim
    ; bagLimitEquiv
    ; isLimitPreservingBag
    ; Bag≃Tote
    ; isGroupoidBagLim
    )

-- The improved bag functor is small:
_ : Type → Type
_ = Bag

-- The "small" and "large" types of bags are equivalent:
Proposition6 : {X : Type} → Bag X ≃ Tote X
Proposition6 = Bag≃Tote

-- 6 The Final Coalgebra in Groupoids

-- The limit of the bag functor is a groupoid:
_ : isGroupoid BagLim
_ = isGroupoidBagLim

module Theorem9 where
  -- Bag preserves limits of terminal co-chains,
  -- i.e. the limit preservation map is an equivalence.
  _ : isLimitPreserving Bag
  _ = isLimitPreservingBag

  -- TODO:
  -- From the above and ???, it follows that `Lim Bag` is the
  -- final coalgebra of Bag.

open import Multiset.FMSet.Fixpoint using (FMSetFixSetTruncTree)

-- The limit obtained from Theorem 9 is also a fixpoint for FMSet.
Theorem10 : FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂
Theorem10 = FMSetFixSetTruncTree

open import Multiset.FMSet.Finality using (isContrAna)

-- Assuming the axiom of choice, ∥ BagLim ∥₂ is the final
-- coalgebra of FMSet in sets, i.e. the space of coalgebra
-- morphisms into it is contractible
Theorem11 = isContrAna

-- 7 Alternatives and Generalizations

-- 7.1 Using Coinductive Types

-- See `Multiset.Coalgebra.FinCoalg` for the details, again --sized-types is needed.
