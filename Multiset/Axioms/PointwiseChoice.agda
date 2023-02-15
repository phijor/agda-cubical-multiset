{-# OPTIONS --safe #-}

module Multiset.Axioms.PointwiseChoice where

open import Multiset.Prelude
open import Multiset.Relation.Base
open import Multiset.Axioms.Choice

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (section)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_])
open import Cubical.Relation.Binary using (Rel ; module BinaryRelation)

private
  variable
    ℓA ℓB ℓR : Level
    A : Type ℓA
    B : Type ℓB

  isSetSeqQuot : ∀ {R : Rel A A ℓR} → isSet (A / R)
  isSetSeqQuot = SQ.squash/

-- pointwise lifting of a relation to a function space
Pointwise : ∀ {ℓ} {X : Type ℓ} → (R : Rel A B ℓR) → Rel (X → A) (X → B) _
Pointwise R f g = ∀ x → R (f x) (g x)

-- the quotient a function space by the pointwise lifted relation
[_⇒_]/_ : (A : Type ℓA) (B : Type ℓB) (R : Rel B B ℓR) → Type _
[ A ⇒ B ]/ R = (A → B) / Pointwise R

module Properties (A : Type ℓA) {B : Type ℓB} (R : Rel B B ℓR) where
  private
    isSetA→B/R : isSet (A → _ / R)
    isSetA→B/R = isSet→ isSetSeqQuot

  -- a function sending equivalence classes of functions wrt. pointwise
  -- lifted relation to functions into equivalence classes
  unwrap : [ A ⇒ B ]/ R → A → B / R
  unwrap = SQ.rec isSetA→B/R eval pres-pw where
    eval : (A → B) → A → B / R
    eval f a = [ f a ]

    pres-pw : (f g : A → B) → Pointwise R f g → eval f ≡ eval g
    pres-pw f g pw = funExt λ a → SQ.eq/ (f a) (g a) (pw a)

  unwrapHasSection : (f : A → B / R) → Type _
  unwrapHasSection f = Σ[ f⁻¹ ∈ ([ A ⇒ B ]/ R) ] (unwrap f⁻¹ ≡ f)

  open BinaryRelation

  effectiveRel→isPropUnwrapSection : (isEffective R) → ∀ f → isProp (unwrapHasSection f)
  effectiveRel→isPropUnwrapSection effectiveR f (g , sec-g) (g' , sec-g') = Σ≡Prop (λ g → isSetA→B/R (unwrap g) f) g≡g' where
    g≡g' : g ≡ g'
    g≡g' = SQ.elimProp2 {P = λ g g' → unwrap g ≡ f → unwrap g' ≡ f → g ≡ g'}
      (λ g g' → isPropΠ2 λ _ _ → isSetSeqQuot g g')
      rec
      g g'
      sec-g sec-g' where module _ (h h' : A → B) (p : unwrap [ h ] ≡ f) (p' : unwrap [ h' ] ≡ f) where
        pw : Pointwise R h h'
        pw a = invIsEq (effectiveR (h a) (h' a)) (funExt⁻ (p ∙ sym p') a)

        rec : [ h ] ≡ [ h' ]
        rec = SQ.eq/ h h' pw

open Properties using (unwrapHasSection) public

open BinaryRelation

PointwiseChoice : (ℓA ℓB ℓR : Level) → Type (ℓ-suc (ℓ-max (ℓ-max ℓA ℓB) ℓR))
PointwiseChoice ℓA ℓB ℓR =
  ∀ (A : Type ℓA) {B : Type ℓB} (R : B → B → Type ℓR)
  → (setA : isSet A) (setB : isSet B) (propR : isPropValued R) (equivR : isEquivRel R)
  → (f : A → B / R) → unwrapHasSection A R f

module PWC (pwc : PointwiseChoice ℓA ℓB ℓR) (A : Type ℓA) (B : Type ℓB) (R : B → B → Type ℓR)
  (setA : isSet A) (setB : isSet B) (propR : isPropValued R) (equivR : isEquivRel R)
  where

  unwrap : [ A ⇒ B ]/ R → A → B / R
  unwrap = Properties.unwrap A R

  θ = unwrap

  wrap : (f : A → B / R) → [ A ⇒ B ]/ R
  wrap f = pwc A R setA setB propR equivR f .fst

  θ⁻¹ = wrap

  unwrap-section : section unwrap wrap
  unwrap-section f = pwc A R setA setB propR equivR f .snd

AC→PointwiseChoice : AC ℓA ℓB (ℓ-max ℓB ℓR) → PointwiseChoice ℓA ℓB ℓR
AC→PointwiseChoice ac A {B} R setA setB propR equivR = pwc where
  []-surjective : ∀ (f : A → B / R) → ∃[ g ∈ (A → B) ] ∀ a → SQ.[ g a ] ≡ f a
  []-surjective f = ac R' setA (λ _ → setB) propR' R'-inv where
    R' : A → B → Type _
    R' a b = [ b ] ≡ f a

    propR' : ∀ a b → isProp (R' a b)
    propR' a b = isSetSeqQuot [ b ] (f a)

    R'-inv : ∀ a → ∃[ b ∈ B ] R' a b
    R'-inv a = SQ.elimProp {P = λ b' → ∃[ b ∈ B ] SQ.[ b ] ≡ b'} (λ _ → PT.isPropPropTrunc) (λ b → PT.∣ b , refl ∣₁) (f a)

  pwc : (f : A → B / R) → unwrapHasSection A R f
  pwc f = PT.rec (Properties.effectiveRel→isPropUnwrapSection A R (SQ.isEquivRel→isEffective propR equivR) f)
    (λ { (g , sec-g) → [ g ] , funExt sec-g })
    ([]-surjective f)
