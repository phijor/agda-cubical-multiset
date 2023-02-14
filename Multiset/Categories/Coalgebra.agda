{-# OPTIONS --safe #-}

module Multiset.Categories.Coalgebra where

open import Multiset.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Reflection.RecordEquiv

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (F : Functor C C) where

  open Category

  open Functor F
    renaming (F-ob to F₀_ ; F-hom to F₁_)

  IsCoalgebra : ob C → Type ℓC'
  IsCoalgebra x = C [ x , F₀ x ]
  
  record Coalgebra : Type (ℓ-max ℓC ℓC') where
    constructor coalgebra
    field
      {carrier} : ob C
      str : IsCoalgebra carrier

  open Coalgebra

  IsCoalgebraHom : (α β : Coalgebra) → C [ carrier α , carrier β ] → Type ℓC'
  IsCoalgebraHom α β f = f ⋆⟨ C ⟩ β .str ≡ α .str ⋆⟨ C ⟩ F₁ f

  isPropIsCoalgebraHom : {α β : Coalgebra} (f : C [ carrier α , carrier β ]) → isProp (IsCoalgebraHom α β f)
  isPropIsCoalgebraHom f = C .isSetHom _ _

  record CoalgebraHom (α β : Coalgebra) : Type ℓC' where
    constructor coalgebraHom
    field
      carrierHom : C [ carrier α , carrier β ]
      strHom : IsCoalgebraHom α β carrierHom
  open CoalgebraHom

  unquoteDecl CoalgebraHomIsoΣ = declareRecordIsoΣ CoalgebraHomIsoΣ (quote CoalgebraHom)

  isSetCoalgebraHom : {α β : Coalgebra} → isSet (CoalgebraHom α β)
  isSetCoalgebraHom = isOfHLevelRetractFromIso 2 CoalgebraHomIsoΣ (isSetΣSndProp (C .isSetHom) isPropIsCoalgebraHom)

  idCoalgebraHom : {α : Coalgebra} → CoalgebraHom α α
  idCoalgebraHom {α} .carrierHom = id C
  idCoalgebraHom {α} .strHom = goal where abstract
    goal : IsCoalgebraHom α α (id C)
    goal =
      id C ⋆⟨ C ⟩ α .str  ≡⟨ ⋆IdL C (α .str) ⟩
      α .str              ≡⟨ sym (⋆IdR C _) ⟩
      α .str ⋆⟨ C ⟩ id C  ≡⟨ cong (λ f → α .str ⋆⟨ C ⟩ f) (sym F-id) ⟩
      F₁ (id C) ∘⟨ C ⟩ α .str ∎

  CoalgebraHom≡ : {α β : Coalgebra} {f g : CoalgebraHom α β}
    → (f .carrierHom ≡ g .carrierHom)
    → f ≡ g
  CoalgebraHom≡ p i .carrierHom = p i
  CoalgebraHom≡ {f = f} {g = g} p i .strHom = isProp→PathP (λ i → isPropIsCoalgebraHom (p i)) (f .strHom) (g .strHom) i

  Coalg⟨_⟩[_,_] = CoalgebraHom

  seqCoalgebraHom : {α β γ : Coalgebra}
    → (f : CoalgebraHom α β)
    → (g : CoalgebraHom β γ)
    → CoalgebraHom α γ
  seqCoalgebraHom f g .carrierHom = f .carrierHom ⋆⟨ C ⟩ g .carrierHom
  seqCoalgebraHom {α} {β} {γ} (coalgebraHom f f-hom) (coalgebraHom g g-hom) .strHom = goal where abstract
    goal : IsCoalgebraHom α γ (f ⋆⟨ C ⟩ g)
    goal =
      (f ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ γ .str        ≡⟨ ⋆Assoc C _ _ _ ⟩
      f ⋆⟨ C ⟩ (g ⋆⟨ C ⟩ γ .str)        ≡⟨ lCatWhisker {C = C} _ _ _ g-hom ⟩
      f ⋆⟨ C ⟩ (β .str ⋆⟨ C ⟩ F₁ g)     ≡⟨ sym (⋆Assoc C _ _ _) ⟩
      (f ⋆⟨ C ⟩ β .str) ⋆⟨ C ⟩ F₁ g     ≡⟨ rCatWhisker {C = C} _ _ _ f-hom ⟩
      (α .str ⋆⟨ C ⟩ F₁ f) ⋆⟨ C ⟩ F₁ g  ≡⟨ ⋆Assoc C _ _ _ ⟩
      α .str ⋆⟨ C ⟩ (F₁ f ⋆⟨ C ⟩ F₁ g)  ≡⟨ lCatWhisker {C = C} _ _ _ (sym (F-seq f g)) ⟩
      α .str ⋆⟨ C ⟩ F₁ (f ⋆⟨ C ⟩ g) ∎

  CoalgebrasCategory : Category (ℓ-max ℓC ℓC') ℓC'
  CoalgebrasCategory .ob = Coalgebra
  CoalgebrasCategory .Hom[_,_] = CoalgebraHom
  CoalgebrasCategory .id = idCoalgebraHom
  CoalgebrasCategory ._⋆_ = seqCoalgebraHom
  CoalgebrasCategory .⋆IdL _ = CoalgebraHom≡ (⋆IdL C _)
  CoalgebrasCategory .⋆IdR _ = CoalgebraHom≡ (⋆IdR C _)
  CoalgebrasCategory .⋆Assoc _ _ _ = CoalgebraHom≡ (⋆Assoc C _ _ _)
  CoalgebrasCategory .isSetHom = isSetCoalgebraHom

  isTerminalCoalgebra : Coalgebra → Type _
  isTerminalCoalgebra = isTerminal CoalgebrasCategory

  TerminalCoalgebra : Type _
  TerminalCoalgebra = Terminal CoalgebrasCategory
