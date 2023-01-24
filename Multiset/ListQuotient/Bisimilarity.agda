{-# OPTIONS --safe #-}

module Multiset.ListQuotient.Bisimilarity where

open import Multiset.Prelude
open import Multiset.ListQuotient.ListFinality
  using
    ( FunctorΣVec
    ; !^
    ; cut
    ; Tree
    ; fix ; fix⁺ ; fix⁻
    ; ΣVecLimitPath
    ; pres ; pres⁺ ; pres⁻
    ; pres-Iso ; pres′ ; pres′⁻
    ; subtree
    )

open import Multiset.Util using (isInjective)
open import Multiset.Util.Vec as Vec hiding (_∈_ ; remove)
open import Multiset.Util.BundledVec as BVec
  using
    ( ΣVec
    ; []
    ; _#∷_
    ; _∈_
    ; remove
    ; Relator∞ ; Relator
    ; rnil∞ ; rcons∞
    ; isReflRelator
    ; isTransRelator
    ; isPropRelator
    ; Relator-map
    )
open import Multiset.Util.Relation
open import Multiset.Util.SetQuotients
  using (relBiimpl→QuotIso)
  renaming (map to map/₂)
open import Multiset.Limit.Chain
  using
    ( lim
    ; Limit
    ; Chain
    ; shift
    ; isPropChain→Limit
    ; isOfHLevelLimit
    ; module Completeness
    )
open import Multiset.Limit.TerminalChain as TerminalChain
  using
    ( Functor
    ; Lim
    ; ShLim
    ; ShLim→Lim
    ; _^_
    )
  -- hiding (pres)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Base as Nat using (ℕ ; suc ; zero)
open import Cubical.Data.Unit.Base using (Unit* ; Unit ; tt* ; tt)
open import Cubical.Data.Unit.Properties using (isOfHLevelUnit*)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.List.Base as List using (List)
open import Cubical.HITs.PropositionalTruncation as PT using ()
open import Cubical.HITs.SetQuotients as SQ using () renaming (_/_ to _/₂_ ; [_] to [_]₂ ; eq/ to eq/₂)
open import Cubical.Relation.Binary using (module BinaryRelation ; pulledbackRel ; RelIso ; Rel)

open BVec.ΣVec
open Limit using (elements ; is-lim)
open Iso
open Functor ⦃...⦄

-- Tot : ∀ {ℓ} {X : Type ℓ} → Rel X X ℓ-zero
-- Tot {X = X} = λ _ _ → Unit

Approx : (n : ℕ) → (s t : ΣVec ^ n) → Type
Approx zero = Tot Unit* _
Approx (suc n) = Relator (Approx n)

isPropApprox : ∀ n (s t : ΣVec ^ n) → isProp (Approx n s t)
isPropApprox zero = isPropTot
isPropApprox (suc n) s t = isPropRelator (Approx n)

Approx-π : ∀ n {s t} → Approx (suc n) s t → Approx n (!^ n s) (!^ n t)
Approx-π zero _ = tt*
Approx-π (suc n) rel = Relator-map (Approx (suc n)) _ (Approx-π n) rel

RelatorLim^ : ℕ → (s t : Lim ΣVec) → Type
RelatorLim^ n s t = Approx n (cut n s) (cut n t)

isPropRelatorLim^ : ∀ s t n → isProp (RelatorLim^ n s t)
isPropRelatorLim^ s t n = isPropApprox n (cut n s) (cut n t)

module _ (s t : Lim ΣVec) where
  RelatorLimSuc→RelatorLim : ∀ n → RelatorLim^ (suc n) s t → RelatorLim^ n s t
  RelatorLimSuc→RelatorLim n rel = subst2 (Approx n) (s .is-lim n) (t .is-lim n) (Approx-π n rel)

  BisimChain : Chain ℓ-zero
  BisimChain .Chain.Ob n = RelatorLim^ n s t
  BisimChain .Chain.π = RelatorLimSuc→RelatorLim

  Bisim : Type
  Bisim = Limit BisimChain

  Bisim→Approx : (n : ℕ) → Bisim → Approx n (cut n s) (cut n t)
  Bisim→Approx n s≈t = s≈t .elements n

  isPropBisim : isProp Bisim
  isPropBisim = isOfHLevelLimit _ 1 (isPropRelatorLim^ s t)

bisim : {s t : Lim ΣVec} → (∀ n → RelatorLim^ n s t) → Bisim s t
bisim {s} {t} = isPropChain→Limit (BisimChain s t) (isPropRelatorLim^ s t)

ShBisimChain : (s t : ShLim ΣVec) → Chain ℓ-zero
ShBisimChain s t .Chain.Ob n = Approx (suc n) (s .elements n) (t .elements n)
ShBisimChain s t .Chain.π n rel = subst2 (Approx (suc n)) (s .is-lim n) (t .is-lim n) (Approx-π (suc n) rel)

ShBisim : Rel (ShLim ΣVec) (ShLim ΣVec) ℓ-zero
ShBisim s t = Limit (ShBisimChain s t)

shbisim : {s t : ShLim ΣVec} → (∀ n → Approx (suc n) (s .elements n) (t .elements n)) → ShBisim s t
shbisim {s} {t} = isPropChain→Limit (ShBisimChain s t) λ n → isPropRelator (Approx n)

infix 5 _≈_ _≈ˢʰ_
_≈_ = Bisim
_≈ˢʰ_ = ShBisim

syntax RelatorLim^ n s t = s ≈[ n ] t

module _ where
  open BinaryRelation

  isReflApprox : ∀ n → isRefl (Approx n)
  isReflApprox zero = isReflTot
  isReflApprox (suc n) = isReflRelator (isReflApprox n)

  isTransApprox : ∀ n → isTrans (Approx n)
  isTransApprox zero = isTransTot
  isTransApprox (suc n) = isTransRelator (isTransApprox n)
  
  isReflBisim : isRefl Bisim
  isReflBisim t = bisim {s = t} {t = t} λ { n → (isReflApprox n (t .elements n)) }

  isTransBisim : isTrans Bisim
  isTransBisim s t u s≈t t≈u = bisim {s = s} {t = u} λ n → isTransApprox n _ _ _ (s≈t .elements n) (t≈u .elements n)

  BisimApproxEquiv : ∀ {s t} → Bisim s t ≃ (∀ n → Approx n (cut n s) (cut n t))
  BisimApproxEquiv {s} {t} = propBiimpl→Equiv (isPropBisim _ _) (isPropΠ (isPropRelatorLim^ s t)) elements bisim

