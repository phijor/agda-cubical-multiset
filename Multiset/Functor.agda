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

module _ where
  open Functor

  _∙F_ : ∀ {ℓ} (F G : Type ℓ → Type ℓ)
    → ⦃ Functor F ⦄
    → ⦃ Functor G ⦄
    → Functor (G ∘ F)
  _∙F_ _ _ ⦃ FF ⦄ ⦃ FG ⦄ .Functor.map = FG .map ∘ FF .map
  _∙F_ _ _ ⦃ FF ⦄ ⦃ FG ⦄ .Functor.map-id = funExt⁻ (cong (FG .map) (map-id-ext FF) ∙ map-id-ext FG)
  _∙F_ _ _ ⦃ FF ⦄ ⦃ FG ⦄ .Functor.map-comp g f = funExt⁻ (cong (FG .map) (map-comp-ext FF g f) ∙ map-comp-ext FG (map FF g) (map FF f))


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

  isNatTrans : (∀ {X : Type ℓ} → F X → G X) → Type (ℓ-suc ℓ)
  isNatTrans η = ∀ {X Y : Type ℓ} (f : X → Y) → η {Y} ∘ F[ f ] ≡ G[ f ] ∘ η {X}

  record NatTrans : Type (ℓ-suc ℓ) where
    constructor nattrans
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

  Equiv→NatEquiv : (η : ∀ {X} → F X ≃ G X) → isNatTrans (equivFun η) → NatEquiv
  Equiv→NatEquiv η is-nat = nattrans (equivFun η) is-nat , equivIsEquiv η

FunctorSIP₀ : ∀ {ℓ} {F G : Type ℓ → Type ℓ} {{FunctorF : Functor F}} {{FunctorG : Functor G}}
  → ({X : Type ℓ} → F X ≃ G X) → F ≡ G
FunctorSIP₀ equivs = funExt λ X → ua (equivs {X})

-- FunctorSIP : ∀ {ℓ} {F G : Type ℓ → Type ℓ} {{FunctorF : Functor F}} {{FunctorG : Functor G}}
--   → (α : NatEquiv F G) → PathP (λ i → Functor (FunctorSIP₀ (NatEquiv→Equiv F G α) i)) FunctorF FunctorG
-- FunctorSIP α = {! !}

idNatTrans : ∀ {ℓ} (F : Type ℓ → Type ℓ) {{F' : Functor F}} → F ⇒ F
idNatTrans F .mor = idfun _
idNatTrans F .is-nat = λ _ → refl


private
  variable
    ℓ : Level
    F G H : Type ℓ → Type ℓ

invNatEquiv : ∀ ⦃ F' : Functor F ⦄ ⦃ G' : Functor G ⦄ → NatEquiv F G → NatEquiv G F
invNatEquiv {ℓ} {F} {G} η@(nattrans η⁺ is-nat , is-equiv) = nattrans η⁻ is-nat-η⁻ , is-equiv-η⁻ where
  open Functor ⦃...⦄

  η⁻ : ∀ {X} → G X → F X
  η⁻ = invIsEq is-equiv

  is-nat-η⁻ : ∀ {X Y} → (f : X → Y) → η⁻ ∘ map f ≡ map f ∘ η⁻
  is-nat-η⁻ {X} {Y} f =
    η⁻ ∘ map f            ≡⟨ cong ((η⁻ ∘ map f) ∘_) (sym (funExt (secIsEq is-equiv))) ⟩
    η⁻ ∘ map f ∘ η⁺ ∘ η⁻  ≡⟨ cong (λ · → η⁻ ∘ · ∘ η⁻) (sym (is-nat f)) ⟩
    η⁻ ∘ η⁺ ∘ map f ∘ η⁻  ≡⟨ cong (λ g → g ∘ (map f ∘ η⁻)) (funExt (retIsEq is-equiv)) ⟩
              map f ∘ η⁻  ∎

  is-equiv-η⁻ : ∀ {X} → isEquiv (η⁻ {X})
  is-equiv-η⁻ {X} = isoToIsEquiv (invIso (equivToIso (NatEquiv→Equiv F G η)))


compNatTrans : ∀ ⦃ F' : Functor F ⦄ ⦃ G' : Functor G ⦄ ⦃ H' : Functor H ⦄
  → NatTrans F G
  → NatTrans G H
  → NatTrans F H
compNatTrans {ℓ} {F} {G} {H} (nattrans η η-nat) (nattrans φ φ-nat) = nattrans (φ ∘ η) isNatTransComp where
  open Functor ⦃...⦄

  isNatTransComp : isNatTrans F H (φ ∘ η)
  isNatTransComp f =
    φ ∘ η ∘ map f ≡⟨ cong (φ ∘_) (η-nat f) ⟩
    φ ∘ map f ∘ η ≡⟨ cong (_∘ η) (φ-nat f) ⟩
    map f ∘ φ ∘ η ∎

_∙ₙₜ_ = compNatTrans

compNatEquiv : ∀ ⦃ F' : Functor F ⦄ ⦃ G' : Functor G ⦄ ⦃ H' : Functor H ⦄
  → NatEquiv F G
  → NatEquiv G H
  → NatEquiv F H
compNatEquiv (η , η-equiv) (φ , φ-equiv) = η ∙ₙₜ φ , equivIsEquiv ((_ , η-equiv) ∙ₑ (_ , φ-equiv))

_∙ₙₑ_ = compNatEquiv

infixr 30 _∙ₙₜ_ _∙ₙₑ_

module SetTruncation where
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂ ; ∣_∣₂)
  open import Multiset.Util.SetTruncation

  open Functor ⦃...⦄

  instance
    setTruncFunctor : Functor {ℓ} ∥_∥₂
    setTruncFunctor .Functor.map = ST.map
    setTruncFunctor .Functor.map-id = ST.elim (λ _ → ST.isSetPathImplicit) (λ _ → refl)
    setTruncFunctor .Functor.map-comp g f = ST.elim (λ _ → ST.isSetPathImplicit) (λ _ → refl)

    setTruncPostFunctor : ⦃ Functor F ⦄ → Functor (∥_∥₂ ∘ F)
    setTruncPostFunctor {F = F} ⦃ F' ⦄ .Functor.map = ST.map ∘ map
    setTruncPostFunctor {F = F} ⦃ F' ⦄ .Functor.map-id = ST.elim (λ _ → ST.isSetPathImplicit) (cong ∣_∣₂ ∘ map-id)
    setTruncPostFunctor {F = F} ⦃ F' ⦄ .Functor.map-comp g f = ST.elim (λ _ → ST.isSetPathImplicit) (cong ∣_∣₂ ∘ map-comp g f)

  setTruncPostNatTrans : ⦃ F' : Functor F ⦄ → ⦃ G' : Functor G ⦄ → F ⇒ G → (∥_∥₂ ∘ F) ⇒ (∥_∥₂ ∘ G)
  setTruncPostNatTrans η .mor = ST.map (η .mor)
  setTruncPostNatTrans η .is-nat f = funExt $ ST.elim (λ _ → ST.isSetPathImplicit) λ x → cong ∣_∣₂ (funExt⁻ (η .is-nat f) x)

  setTruncPostNatEquiv : ⦃ F' : Functor F ⦄ → ⦃ G' : Functor G ⦄ → NatEquiv F G → NatEquiv (∥_∥₂ ∘ F) (∥_∥₂ ∘ G)
  setTruncPostNatEquiv (α , α-equiv) = setTruncPostNatTrans α , equivIsEquiv (setTruncEquiv (_ , α-equiv))
