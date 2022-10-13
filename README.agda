{-# OPTIONS --safe #-}

module README where

open import Multiset.Prelude

open import Cubical.Foundations.Isomorphism using (Iso)
import Cubical.Data.Nat as Nat using (ℕ)
import Cubical.Data.List as List
import Cubical.HITs.SetQuotients as SQ

-- 3. The Finite Bag Functor in Sets

-- 3.1 The free commutative monoid

-- Definition as a HIT
import Multiset.Inductive
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
import Multiset.Equivalences.Inductive-PList

-- Equivalences of FCM and a HIT of head-permuted lists,
-- defined in Cubical.HITs.FiniteMultiset.
import Multiset.Equivalences.Inductive-HeadPList

-- Relational lifting
import Multiset.ListQuotient.Base
  using (DRelator ; Relator)

-- 3.3 As an Analytic Functor

import Multiset.OverSet.Base
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
import Multiset.OverSet.Properties using (module STInvariance)
open Multiset.OverSet.Properties.STInvariance
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
open import Multiset.Chains.FunctorChain
  using
    ( Lim -- The limit of a type-functor
    )
open import Multiset.Inductive.Limit
  using
    ( diag-ysᶜ-islim-alternating
    ; zip-inj⇒complete
    )
  renaming ( zip₁ to pres ) -- The limit preservation map

Lemma2 = diag-ysᶜ-islim-alternating

-- Injectivity of pres implies LLPO.
-- We prove completeness, which implies LLPO.
Theorem2 = zip-inj⇒complete

-- Bonus: Using the equivalent type (List X / Perm), we
-- can even show that LLPO implies the injectivity of the
-- limit-preservation map.
open import Multiset.ListQuotient.ToInjectivity
  using (llpo⇒zip-inj)

open import Multiset.OverSet.Limit using (module Surjectivity)

-- The limit preservation map is surjective.
∥Theorem4∥ = Surjectivity.inhFibers

-- 4.2 As a Quotient of the Final List-Coalgebra

-- TODO: link the following theorems
-- Theorem 5
-- Theorem 6
-- Theorem 7

-- 5 The Finite Bag Functor in Groupoids

open import Multiset.OverGroupoid
  using (FMSet≃∥Tote∥₂)
  renaming
    ( FMSet to Tote -- The type of large bags.
    ; isGroupoidFMSet to isGroupoidTote
    )

-- Note that the universe level goes up by one:
_ : Type → Type₁
_ = Tote

Proposition4 : {X : Type} → isGroupoid X → isGroupoid (Tote X)
Proposition4 = isGroupoidTote

-- The definition in groupoinds, when truncated yields the definition in sets:
Theorem8 = FMSet≃∥Tote∥₂

-- Theorem 10:
-- The equivalence FMSet ∥ BagLim ∥₂ ≃ ∥ BagLim ∥₂ lives in the following module:
--
--  open import Multiset.OverSet.Fixpoint
--
-- The proof is complete, but Agda loops when trying to type-check the equivalence.
-- Ironically, this happens when trying to show (Σ A B) ≃ (Σ A B') from B ≃ B', which
-- should not pose a problem at all!

-- The small axiomatization:
open import Multiset.OverBij
  using
    ( Bag
    ; bagLimitIso
    ; module Unzip
    ; zipUnzipIso
    ; zipUnzipIsoInv≡unzipped
    )

-- The improved bag functor is small:
_ : Type → Type
_ = Bag

-- The limit preservation map is an equivalence.
Theorem9 = zipUnzipIso

-- The theorem constructs an explicit isomorphism
-- in a series of steps.
Bag-pres = Unzip.unzipped

-- The map underlying the isomorphism in Theorem 9 is indeed the limit preservation map.
_ : zipUnzipIso .Iso.inv ≡ Unzip.unzipped
_ = zipUnzipIsoInv≡unzipped
