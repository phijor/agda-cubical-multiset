{-# OPTIONS --safe #-}

module Multiset.Setoid.Base where

open import Multiset.Prelude
open import Multiset.Relation.Base as Relation hiding (RelOf)
open import Multiset.Util.Relation using ()

open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure using (TypeWithStr)
open import Cubical.Foundations.Structure using (⟨_⟩ ; str) public
open import Cubical.HITs.SetQuotients as SQ using (_/_)
open import Cubical.Relation.Binary using (Rel ; module BinaryRelation)

open RelationStr using (rel ; is-relation)

record SetoidStr {ℓ} (ℓR : Level) (S : Type ℓ) : Type (ℓ-max ℓ (ℓ-suc ℓR)) where
  field
    rel : Rel S S ℓR
    is-relation : IsRelation rel
    is-equiv-rel : BinaryRelation.isEquivRel rel

  open BinaryRelation.isEquivRel is-equiv-rel public


Setoid : (ℓ ℓR : Level) → Type (ℓ-suc (ℓ-max ℓ ℓR))
Setoid ℓ ℓR = TypeWithStr ℓ (SetoidStr ℓR)

Setoid→Relation : ∀ {ℓ ℓR} → Setoid ℓ ℓR → Relation ℓ ℓR
Setoid→Relation s .fst = ⟨ s ⟩
Setoid→Relation s .snd .rel = str s .SetoidStr.rel
Setoid→Relation s .snd .is-relation = str s .SetoidStr.is-relation

Relation→Setoid : ∀ {ℓ ℓR} → (R : Relation ℓ ℓR)
  → BinaryRelation.isEquivRel (Relation.RelOf R)
  → Setoid ℓ ℓR
Relation→Setoid R equivR .fst = ⟨ R ⟩
Relation→Setoid R equivR .snd .SetoidStr.rel = str R .rel
Relation→Setoid R equivR .snd .SetoidStr.is-relation = str R .is-relation
Relation→Setoid R equivR .snd .SetoidStr.is-equiv-rel = equivR

private
  _ʳ = Setoid→Relation

module _ {ℓ ℓR : Level} where
  module _ (R : Setoid ℓ ℓR) where
    RelOf : Rel ⟨ R ⟩ ⟨ R ⟩ ℓR
    RelOf = str R .SetoidStr.rel

    isSetSetoid : isSet ⟨ R ⟩
    isSetSetoid = str R .SetoidStr.is-relation .IsRelation.is-set-carrier

    isPropValuedRel : BinaryRelation.isPropValued RelOf
    isPropValuedRel = str R .SetoidStr.is-relation .IsRelation.is-prop-rel

    isRelation : IsRelation RelOf
    isRelation = str R .SetoidStr.is-relation

    isEquivRel : BinaryRelation.isEquivRel RelOf
    isEquivRel = str R .SetoidStr.is-equiv-rel

  PreSetoidHom : (R S : Setoid ℓ ℓR) → Type (ℓ-max ℓ ℓR)
  PreSetoidHom R S = Rel[ R ʳ ⇒ S ʳ ]

  SetoidHomEq : (R S : Setoid ℓ ℓR) → (f g : PreSetoidHom R S) → Type _
  SetoidHomEq R S f g = (x : ⟨ R ⟩) → (f .morphism x) ≈⟨ S ʳ ⟩ (g .morphism x) where
    open Rel[_⇒_]

  SetoidHom : (R S : Setoid ℓ ℓR) → Type (ℓ-max ℓ ℓR)
  SetoidHom R S = PreSetoidHom R S / SetoidHomEq R S

  setoidhom : {R S : Setoid ℓ ℓR} → PreSetoidHom R S → SetoidHom R S
  setoidhom = SQ.[_]

  -- SetoidHomElim : ∀ {ℓ'} {R S : Setoid ℓ ℓR} → {B : SetoidHom R S → Type ℓ'}
  --   → (∀ f → isSet (B f))
  --   → (morphism* : (f : ⟨ R ⟩ → ⟨ S ⟩) → (p : Relation.PreservesRelation (R ʳ) (S ʳ) f) → B SQ.[ rel⇒ f p ])
  --   → (eq : ∀ {f g : ⟨ R ⟩ → ⟨ S ⟩} → ?)
  --   → (f : SetoidHom R S) → B f
  -- SetoidHomElim {R = R} {S = S} {B = B} setB morphism* eq = go where
  --   go : (f : SetoidHom R S) → B f
  --   go = SQ.elim setB
  --     (λ { (rel⇒ morphism preserves-relation) → morphism* morphism preserves-relation })
  --     λ { a b r → {!Relation.Rel⇒Path !} }


  module _ {R S : Setoid ℓ ℓR} where
    open Rel[_⇒_]
    open SetoidStr
    open BinaryRelation hiding (isEquivRel)

    isReflSetoidHomEq : isRefl (SetoidHomEq R S)
    isReflSetoidHomEq f r = (str S) .reflexive (f .morphism r)

    isSymSetoidHomEq : isSym (SetoidHomEq R S)
    isSymSetoidHomEq f g f≈g x = str S .symmetric _ _ (f≈g x)

    isTransSetoidHomEq : isTrans (SetoidHomEq R S)
    isTransSetoidHomEq f g h f≈g g≈h x = str S .transitive _ _ _ (f≈g x) (g≈h x)

    isEquivRelSetoidHomEq : BinaryRelation.isEquivRel (SetoidHomEq R S)
    isEquivRelSetoidHomEq .BinaryRelation.isEquivRel.reflexive = isReflSetoidHomEq
    isEquivRelSetoidHomEq .BinaryRelation.isEquivRel.symmetric = isSymSetoidHomEq
    isEquivRelSetoidHomEq .BinaryRelation.isEquivRel.transitive = isTransSetoidHomEq

    isPropValuedSetoidHomEq : {R S : Setoid ℓ ℓR} → isPropValued (SetoidHomEq R S)
    isPropValuedSetoidHomEq {S = S} = λ f g → isPropΠ λ x → isPropValuedRel S (f .morphism x) (g .morphism x)

    effective :
      ∀ {f g : PreSetoidHom R S}
      → setoidhom f ≡ setoidhom g
      → SetoidHomEq R S f g
    effective {f} {g} = SQ.effective isPropValuedSetoidHomEq isEquivRelSetoidHomEq f g

  isSetSetoidHom : {R S : Setoid ℓ ℓR} → isSet (SetoidHom R S)
  isSetSetoidHom = SQ.squash/

  SetoidIdHom : {S : Setoid ℓ ℓR} → SetoidHom S S
  SetoidIdHom {S} = SQ.[ idRel⇒ {S = S ʳ} ]

  _⋆_ : {R S T : Setoid ℓ ℓR} → SetoidHom R S → SetoidHom S T → SetoidHom R T
  _⋆_ {R} {S} {T} = SQ.setQuotBinOp isReflSetoidHomEq isReflSetoidHomEq _⋆Rel⇒_ pres where
    open Rel[_⇒_]
    open SetoidStr

    pres :
      ∀ (f f' : PreSetoidHom R S)
      → (g g' : PreSetoidHom S T)
      → SetoidHomEq R S f f'
      → SetoidHomEq S T g g'
      → SetoidHomEq R T (f ⋆Rel⇒ g) (f' ⋆Rel⇒ g')
    pres f f' g g' f-rel g-rel r = goal where
      goal : (g .morphism (f .morphism r)) ≈⟨ T ʳ ⟩ (g' .morphism (f' .morphism r))
      goal = (str T) .transitive _ _ _ (g-rel _) (g' .preserves-relation (f-rel r))

  ⋆IdL : {R S : Setoid ℓ ℓR} → (f : SetoidHom R S) → SetoidIdHom ⋆ f ≡ f
  ⋆IdL = SQ.elimProp (λ _ → isSetSetoidHom _ _) λ f → cong SQ.[_] (⋆Rel⇒IdL f)

  ⋆IdR : {R S : Setoid ℓ ℓR} → (f : SetoidHom R S) → f ⋆ SetoidIdHom ≡ f
  ⋆IdR = SQ.elimProp (λ _ → isSetSetoidHom _ _) λ f → cong SQ.[_] (⋆Rel⇒IdR f)

  ⋆Assoc : {R S T U : Setoid ℓ ℓR}
    → (f : SetoidHom R S)
    → (g : SetoidHom S T)
    → (h : SetoidHom T U)
    → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  ⋆Assoc = SQ.elimProp3 (λ _ _ _ → isSetSetoidHom _ _) λ f g h → cong SQ.[_] (⋆Rel⇒Assoc f g h)
