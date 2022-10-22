{-# OPTIONS --safe #-}

-- Prerequisites
-- -------------
--
-- This library has been tested with the following software versions:
--  * Agda v2.6.2.2
--  * The Cubical library, commit ce3120d3f (25th May 2022):
--      https://github.com/agda/cubical/tree/ce3120d3f8d692847b2744162bcd7a01f0b687eb
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

open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Data.FinSet using (FinSet)
import Cubical.Data.Nat as Nat using (ℕ)
import Cubical.Data.List as List
import Cubical.HITs.SetQuotients as SQ

-- 3. The Finite Bag Functor in Sets

-- 3.1 The free commutative monoid

-- Definition as a HIT
import Multiset.FCM
  renaming
    (M to FCM)
  using
    (rec ; elim)

-- 3.2 As a Quotient of Lists

-- Lists modulo permutations
open import Multiset.Ordering.Order
  using (Perm)
  renaming (Mset to List[_]/Perm)

-- Equivalences of FCM and lists module permutations.
import Multiset.Equivalences.FCM-PList

-- Equivalences of FCM and a HIT of head-permuted lists,
-- defined in Cubical.HITs.FiniteMultiset.
import Multiset.Equivalences.FCM-HeadPList

-- Relational lifting
import Multiset.ListQuotient.Base
  using (DRelator ; Relator)

-- 3.3 As an Analytic Functor

import Multiset.FMSet.Base
  using (_∼_ ; FMSet)
  renaming (SymmetricAction to SymAct)

open import Multiset.FiniteChoice
  using
    (box ; unbox ; setFinChoice≃
    ; elimₙ ; elimₙ-comp
    )

-- The equivalence built from `box`:
Lemma1 : _
Lemma1 = setFinChoice≃

-- The finite choice principle obtained from Lemma 1:
elim∥_∥₂-fin = elimₙ
elim∥_∥₂-finᵝ = elimₙ-comp

-- Theorem 1: FMSet is invariant under set truncation.
import Multiset.FMSet.Properties using (module STInvariance)
open Multiset.FMSet.Properties.STInvariance
  renaming (STInvarianceEquiv to FMSet∥-∥₂≃FMSet)


-- 3.4 Definable Quotients and Sorting
open import Multiset.Ordering.Order
  using
    ( isLinOrder -- Definition of a linear order
    ; module Sorting -- Contains insertion sort
    ; module ListLinOrder
    )

module _ {A : Type} (setA : isSet A) (R : A → A → Type) (linR : isLinOrder R) where
  module S = Sorting setA R linR

  -- Extracting a sorted list from a list modulo permutation
  sortPerm : List[ A ]/Perm → List.List A
  sortPerm = S.sortMset

  -- Extraction is a section of the set quotient constructor
  sortPerm-section : ∀ xs → SQ.[ S.sortMset xs ] ≡ xs
  sortPerm-section = S.sortMset-section

-- TODO: Proposition 1 & 2

  module L = ListLinOrder setA R linR

  -- Lexicographic order on lists
  Lex : List.List A → List.List A → Type
  Lex = L.Lex

  linLex : isLinOrder Lex
  linLex = L.linLex

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

open import Multiset.FMSet.Limit using (module Surjectivity)

-- The limit preservation map is surjective.
∥Theorem4∥ = Surjectivity.inhFibers

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
    ; bagLimitEquiv
    ; zipUnzipIso
    ; zipUnzipIsoInv≡pres
    )

-- The improved bag functor is small:
_ : Type → Type
_ = Bag

-- XXX: The proof of Proposition 6 (Bag X ≃ Tote X) runs into an issue when typechecking.
-- See the note on Theorem 10 below.

-- 6 The Final Coalgebra in Groupoids

-- The limit preservation map is an equivalence.
Theorem9 = zipUnzipIso

-- The map underlying the isomorphism in Theorem 9 is indeed the limit preservation map.
_ : zipUnzipIso .Iso.inv ≡ pres Bag
_ = zipUnzipIsoInv≡pres

open import Multiset.FMSet.Fixpoint using (FMSetFixSetTruncTree)

-- The fixpoint of FMSet,  (FMSet ∥ BagLim ∥₂) ≃ ∥ BagLim ∥₂
-- NOTE: The proof is complete, but Agda loops when trying to type-check the equivalence.
-- Ironically, this happens when trying to show (Σ A B) ≃ (Σ A B') from ∀ x → B x ≃ B' x,
-- which should not pose a problem at all!
Theorem10 = FMSetFixSetTruncTree

open import Multiset.FMSet.Finality using (isContrAna)

-- Assuming the axiom of choice, ∥ BagLim ∥₂ is the final
-- coalgebra of FMSet in sets, i.e. the space of coalgebra
-- morphisms into it is contractible
Theorem11 = isContrAna

-- 7 Alternatives and Generalizations

-- 7.1 Using Coinductive Types

-- See `Multiset.Coalgebra.FinCoalg` for the details, again --sized-types is needed.
