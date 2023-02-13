{-# OPTIONS --safe #-}

module Multiset.Relation.Base where

open import Multiset.Prelude
open import Multiset.Util.Relation public

open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩ ; str) public
open import Cubical.Reflection.RecordEquiv using (declareRecordIsoΣ)
open import Cubical.Relation.Binary using (Rel ; module BinaryRelation)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)

private
  variable
    ℓ ℓ′ ℓ≈ ℓ≈′ : Level

open BinaryRelation using (isRefl ; isSym ; isTrans ; isEquivRel ; isPropValued)

record IsRelation {A : Type ℓ} (_≈_ : Rel A A ℓ≈) : Type (ℓ-max ℓ ℓ≈) where
  no-eta-equality
  field
    is-set-carrier : isSet A
    is-prop-rel : isPropValued _≈_

record RelationStr (ℓ≈ : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ≈)) where
  no-eta-equality
  field
    rel : Rel A A ℓ≈
    is-relation : IsRelation rel

  open IsRelation is-relation public

Relation : (ℓ ℓ≈ : Level) → Type _
Relation ℓ ℓ≈ = TypeWithStr ℓ (RelationStr ℓ≈)

RelOf : (S : Relation ℓ ℓ≈) → Rel ⟨ S ⟩ ⟨ S ⟩ ℓ≈
RelOf S = str S .RelationStr.rel

syntax RelOf S a b = a ≈⟨ S ⟩ b

module _ {ℓ ℓ≈ ℓ′ ℓ≈′ : Level} (S : Relation ℓ ℓ≈) (R : Relation ℓ′ ℓ≈′) where
  open IsRelation
  open RelationStr

  PreservesRelation : (f : ⟨ S ⟩ → ⟨ R ⟩) → Type (ℓ-max (ℓ-max ℓ ℓ≈) ℓ≈′)
  PreservesRelation f = ∀ {a b : ⟨ S ⟩} → a ≈⟨ S ⟩ b → f a ≈⟨ R ⟩ f b

  isPropPreservesRelation : {f : ⟨ S ⟩ → ⟨ R ⟩} → isProp (PreservesRelation f)
  isPropPreservesRelation = isPropImplicitΠ2 λ _ _ → isPropΠ λ _ → str R .is-prop-rel _ _

  record Rel[_⇒_] : Type (ℓ-max (ℓ-max ℓ ℓ′) (ℓ-max ℓ≈ ℓ≈′)) where
    field
      morphism : ⟨ S ⟩ → ⟨ R ⟩
      preserves-relation : PreservesRelation morphism

  open Rel[_⇒_]
  Rel⇒IsoΣ : Iso Rel[_⇒_] (Σ (⟨ S ⟩ → ⟨ R ⟩) PreservesRelation)
  Rel⇒IsoΣ .Iso.fun f .fst = f .morphism
  Rel⇒IsoΣ .Iso.fun f .snd = f .preserves-relation
  Rel⇒IsoΣ .Iso.inv p .morphism = p .fst
  Rel⇒IsoΣ .Iso.inv p .preserves-relation = p .snd
  Rel⇒IsoΣ .Iso.rightInv p = refl
  Rel⇒IsoΣ .Iso.leftInv f = refl

  isSetRel⇒ : isSet Rel[_⇒_]
  isSetRel⇒ = isOfHLevelRetractFromIso 2 Rel⇒IsoΣ (isSetΣSndProp (isSet→ (str R .is-set-carrier)) λ _ → isPropPreservesRelation)

module _ where
  open Rel[_⇒_]

  private
    variable
      ℓ₀ ℓ₁ ℓ₂ ℓ₃ : Level
      ℓR₀ ℓR₁ ℓR₂ ℓR₃ : Level

  Rel⇒Path : ∀ {R : Relation ℓ ℓ≈} {S : Relation ℓ′ ℓ≈′}
    → {f g : Rel[ R ⇒ S ]}
    → f .morphism ≡ g .morphism
    → f ≡ g
  Rel⇒Path p i .morphism = p i
  Rel⇒Path {R = R} {S} {f} {g} p i .preserves-relation =
    isProp→PathP (λ i → isPropPreservesRelation R S {f = p i}) (f .preserves-relation) (g .preserves-relation) i

  idRel⇒ : {S : Relation ℓ ℓ≈} → Rel[ S ⇒ S ]
  idRel⇒ {S = S} .morphism = idfun ⟨ S ⟩
  idRel⇒ {S = S} .preserves-relation {s₀} {s₁} = idfun (RelOf S s₀ s₁)

  module _
    {R₀ : Relation ℓ₀ ℓR₀}
    {R₁ : Relation ℓ₁ ℓR₁}
    {R₂ : Relation ℓ₂ ℓR₂}
    where

    compPreservesRelation : ∀ {f g}
      → PreservesRelation R₀ R₁ f
      → PreservesRelation R₁ R₂ g
      → PreservesRelation R₀ R₂ (g ∘ f)
    compPreservesRelation pres-f pres-g = pres-g ∘ pres-f

    compRel⇒ : Rel[ R₀ ⇒ R₁ ] → Rel[ R₁ ⇒ R₂ ] → Rel[ R₀ ⇒ R₂ ]
    compRel⇒ f g .morphism = g .morphism ∘ f .morphism
    compRel⇒ f g .preserves-relation = compPreservesRelation (f .preserves-relation) (g .preserves-relation)

    _⋆Rel⇒_ = compRel⇒

    infixl 9 _⋆Rel⇒_

  ⋆Rel⇒IdL : {R : Relation ℓ ℓ≈} {S : Relation ℓ′ ℓ≈′}
    (f : Rel[ R ⇒ S ]) → idRel⇒ ⋆Rel⇒ f ≡ f
  ⋆Rel⇒IdL _ = refl

  ⋆Rel⇒IdR : {R : Relation ℓ ℓ≈} {S : Relation ℓ′ ℓ≈′}
    (f : Rel[ R ⇒ S ]) → f ⋆Rel⇒ idRel⇒ ≡ f
  ⋆Rel⇒IdR _ = refl

  module _
    {R₀ : Relation ℓ₀ ℓR₀}
    {R₁ : Relation ℓ₁ ℓR₁}
    {R₂ : Relation ℓ₂ ℓR₂}
    {R₃ : Relation ℓ₃ ℓR₃} where

    ⋆Rel⇒Assoc :
      (f : Rel[ R₀ ⇒ R₁ ])
      (g : Rel[ R₁ ⇒ R₂ ])
      (h : Rel[ R₂ ⇒ R₃ ])
      → (f ⋆Rel⇒ g) ⋆Rel⇒ h ≡ f ⋆Rel⇒ (g ⋆Rel⇒ h)
    ⋆Rel⇒Assoc f g h = refl
