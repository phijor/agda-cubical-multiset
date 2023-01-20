{-# OPTIONS --safe #-}

module Multiset.Functor where

open import Multiset.Prelude

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)

record Functor {ℓ} (F : Type ℓ → Type ℓ) : Type (ℓ-suc ℓ) where
  field
    map : ∀ {X Y : Type ℓ} → (X → Y) → (F X → F Y)
    map-id : ∀ {X} x → map (idfun X) x ≡ x
    map-comp : ∀ {X Y Z}
      → (g : Y → Z)
      → (f : X → Y)
      → ∀ x → map (g ∘ f) x ≡ map g (map f x)

  map-id-ext : ∀ {X} → map (idfun X) ≡ idfun (F X)
  map-id-ext = funExt map-id

  map-comp-ext : ∀ {X Y Z}
    → (g : Y → Z) → (f : X → Y)
    → map (g ∘ f) ≡ map g ∘ map f
  map-comp-ext g f = funExt (map-comp g f)

  cong-map-ext : ∀ {X Y} → {f g : X → Y}
    → f ≡ g → ∀ x → map f x ≡ map g x
  cong-map-ext p x = cong (λ h → map h x) p

  cong-map : ∀ {X Y} → {f g : X → Y}
    → (∀ x → f x ≡ g x) → ∀ x → map f x ≡ map g x
  cong-map p x = cong (λ h → map h x) (funExt p)


module _ {ℓ} (F : Type ℓ → Type ℓ) {{F' : Functor F}} where
  open Iso

  open Functor F' renaming (map to F[_])

  isoLift : {X Y : Type ℓ} (isom : Iso X Y) → Iso (F X) (F Y)
  isoLift isom .fun = F[ isom .fun ]
  isoLift isom .inv = F[ isom .inv ]
  isoLift isom .rightInv y = sym (map-comp (isom .fun) (isom .inv) y) ∙∙ cong-map (isom .rightInv) y ∙∙ map-id y
  isoLift isom .leftInv x = sym (map-comp (isom .inv) (isom .fun) x) ∙∙ cong-map (isom .leftInv) x ∙∙ map-id x

  equivLift : {X Y : Type ℓ} → X ≃ Y → F X ≃ F Y
  equivLift e = isoToEquiv (isoLift (equivToIso e))

  isEquivFunctorAction : {X Y : Type ℓ} {f : X → Y} → isEquiv f → isEquiv F[ f ]
  isEquivFunctorAction {f = f} is-equiv = equivIsEquiv (equivLift (f , is-equiv))

module _ {ℓ} (F G : Type ℓ → Type ℓ) {{F' : Functor F}} {{G' : Functor G}} where
  open Functor F' using () renaming (map to F[_])
  open Functor G' using () renaming (map to G[_])

  isNatTrans : (∀ {X} → F X → G X) → Type (ℓ-suc ℓ)
  isNatTrans η = ∀ {X Y : Type ℓ} (f : X → Y) → η {Y} ∘ F[ f ] ≡ G[ f ] ∘ η {X}

  record NatTrans : Type (ℓ-suc ℓ) where
    field
      mor : ∀ {X} → F X → G X
      is-nat : isNatTrans mor

    component : ∀ X → F X → G X
    component _ = mor

  _⇒_ : Type _
  _⇒_ = NatTrans

  open NatTrans public

  NatEquiv : Type (ℓ-suc ℓ)
  NatEquiv = Σ[ η ∈ NatTrans ] (∀ {X} → isEquiv (component η X))

  NatEquiv→Equiv : NatEquiv → ∀ {X} → F X ≃ G X
  NatEquiv→Equiv (η , is-equiv) {X} = component η X , is-equiv {X}

FunctorSIP₀ : ∀ {ℓ} {F G : Type ℓ → Type ℓ} {{FunctorF : Functor F}} {{FunctorG : Functor G}}
  → ({X : Type ℓ} → F X ≃ G X) → F ≡ G
FunctorSIP₀ equivs = funExt λ X → ua (equivs {X})

-- FunctorSIP : ∀ {ℓ} {F G : Type ℓ → Type ℓ} {{FunctorF : Functor F}} {{FunctorG : Functor G}}
--   → (α : NatEquiv F G) → PathP (λ i → Functor (FunctorSIP₀ (NatEquiv→Equiv F G α) i)) FunctorF FunctorG
-- FunctorSIP α = {! !}

idNatTrans : ∀ {ℓ} (F : Type ℓ → Type ℓ) {{F' : Functor F}} → F ⇒ F
idNatTrans F .mor = idfun _
idNatTrans F .is-nat = λ _ → refl
