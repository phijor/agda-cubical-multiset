{-# OPTIONS --safe #-}

module Multiset.Setoid.Base where

open import Multiset.Prelude
open import Multiset.Util.Relation using ()

open import Cubical.Foundations.Structure using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩ ; str) public
open import Cubical.Relation.Binary using (Rel ; module BinaryRelation)

private
  variable
    ℓ ℓ′ ℓ≈ ℓ≈′ : Level

isPropRel : ∀ {ℓR} {A B : Type ℓ} → (R : Rel A B ℓR) → Type _
isPropRel {A = A} {B = B} R = {a : A} {b : B} → isProp (R a b)

open BinaryRelation using (isRefl ; isSym ; isTrans ; isEquivRel)

record IsSetoid {A : Type ℓ} (_≈_ : Rel A A ℓ≈) : Type (ℓ-max ℓ ℓ≈) where
  field
    is-set-carrier : isSet A
    is-equiv-rel : isEquivRel _≈_
    is-prop-rel : isPropRel _≈_

  open isEquivRel is-equiv-rel renaming
    ( reflexive to is-reflexive
    ; symmetric to is-symmetric
    ; transitive to is-transitive
    )
    public

record SetoidStr (ℓ≈ : Level) (A : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓ≈)) where
  field
    rel : Rel A A ℓ≈
    is-setoid : IsSetoid rel

  open IsSetoid is-setoid public

Setoid : (ℓ ℓ≈ : Level) → Type _
Setoid ℓ ℓ≈ = TypeWithStr ℓ (SetoidStr ℓ≈)

makeSetoid : {S : Type ℓ} → (R : Rel S S ℓ≈)
  → isSet S
  → isPropRel R
  → isRefl R
  → isSym R
  → isTrans R
  → Setoid ℓ ℓ≈
makeSetoid {S = S} R setS Rprop Rreflexive Rsymmetric Rtransitive = go where
  open IsSetoid
  open SetoidStr
  open isEquivRel

  go : Setoid _ _
  go .fst = S
  go .snd .rel = R
  go .snd .is-setoid .is-set-carrier = setS
  go .snd .is-setoid .is-equiv-rel .reflexive = Rreflexive
  go .snd .is-setoid .is-equiv-rel .symmetric = Rsymmetric
  go .snd .is-setoid .is-equiv-rel .transitive = Rtransitive
  go .snd .is-setoid .is-prop-rel = Rprop

RelOf : (S : Setoid ℓ ℓ≈) → Rel ⟨ S ⟩ ⟨ S ⟩ ℓ≈
RelOf S = str S .SetoidStr.rel

syntax RelOf S a b = a ≈⟨ S ⟩ b

IsSetoidMorphism : (S : Setoid ℓ ℓ≈) (R : Setoid ℓ′ ℓ≈′) (f : ⟨ S ⟩ → ⟨ R ⟩) → Type (ℓ-max (ℓ-max ℓ ℓ≈) ℓ≈′)
IsSetoidMorphism S R f = ∀ {a b : ⟨ S ⟩} → a ≈⟨ S ⟩ b → f a ≈⟨ R ⟩ f b

record SetoidMorphism (S : Setoid ℓ ℓ≈) (R : Setoid ℓ′ ℓ≈′) : Type (ℓ-max (ℓ-max ℓ ℓ′) (ℓ-max ℓ≈ ℓ≈′)) where
  field
    morphism : ⟨ S ⟩ → ⟨ R ⟩
    is-setoid-morphism : IsSetoidMorphism S R morphism
