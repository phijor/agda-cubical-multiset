{-# OPTIONS --safe #-}

module Multiset.Util.SetTruncation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
  using
    ( _∘_
    ; const
    )
open import Cubical.Foundations.Equiv

open import Cubical.HITs.SetTruncation as ST
  using
    ( ∥_∥₂
    ; ∣_∣₂
    ; isSetSetTrunc
    )

private
  variable
    ℓ ℓ' : Level
    X A : Type ℓ
    B : X → Type ℓ'

∣_∣₂∗ : ((a : A) → B a) → ((a : A) → ∥ B a ∥₂)
∣ f ∣₂∗ = λ a → ∣ f a ∣₂

mapId : (∣x∣ : ∥ X ∥₂)
  → ST.map (λ x → x) ∣x∣ ≡ ∣x∣
mapId = ST.elim (λ _ → ST.isSetPathImplicit) λ _ → refl

private
  isSetSetPathImplicit : isSet X → {x y : X} → isSet (x ≡ y)
  isSetSetPathImplicit setX = isProp→isSet (setX _ _)

rec∘map : ∀ {ℓy ℓz} {Y : Type ℓy} {Z : Type ℓz}
  → (setZ : isSet Z)
  → (f : X → Y)
  → (g : Y → Z)
  → (x : ∥ X ∥₂)
  → ST.rec setZ g (ST.map f x) ≡ ST.rec setZ (g ∘ f) x
rec∘map setZ f g = ST.elim (λ _ → isSetSetPathImplicit setZ) λ _ → refl

map∘map : ∀ {ℓx ℓy ℓz} {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓz}
  → (f : X → Y)
  → (g : Y → Z)
  → (x : ∥ X ∥₂)
  → ST.map g (ST.map f x) ≡ ST.map (g ∘ f) x
map∘map f g = rec∘map isSetSetTrunc f (∣_∣₂ ∘ g)

map2 : ∀ {ℓy ℓz} {Y : Type ℓy} {Z : Type ℓz}
  → (f : X → Y → Z)
  → ∥ X ∥₂ → ∥ Y ∥₂ → ∥ Z ∥₂
map2 f = ST.rec2 ST.isSetSetTrunc λ x y → ∣ f x y ∣₂

rec∘map2 : ∀ {ℓy ℓz ℓw} {Y : Type ℓy} {Z : Type ℓz} {W : Type ℓw}
  → (setZ : isSet Z)
  → (f : X → W → Y)
  → (g : Y → Z)
  → (x : ∥ X ∥₂)
  → (w : ∥ W ∥₂)
  → ST.rec setZ g (map2 f x w) ≡ ST.rec2 setZ (λ x w → g (f x w)) x w
rec∘map2 {Z = Z} setZ f g = ST.elim2 (λ _ _ → isSetSetPathImplicit setZ) λ _ _ → refl

map∘map2 : ∀ {ℓy ℓz ℓw} {Y : Type ℓy} {Z : Type ℓz} {W : Type ℓw}
  → (g : Y → Z)
  → (f : X → W → Y)
  → (x : ∥ X ∥₂)
  → (w : ∥ W ∥₂)
  → ST.map g (map2 f x w) ≡ map2 (λ x w → g (f x w)) x w
map∘map2 g f = rec∘map2 ST.isSetSetTrunc f (∣_∣₂ ∘ g)

rec2ConstLeft :  ∀ {ℓz ℓw} {Z : Type ℓz} {W : Type ℓw}
  → (setZ : isSet Z)
  → (f : W → Z)
  → (x : ∥ X ∥₂)
  → (w : ∥ W ∥₂)
  → ST.rec2 setZ (λ x w → f w) x w ≡ ST.rec setZ f w
rec2ConstLeft setZ f = ST.elim2 (λ _ _ → isSetSetPathImplicit setZ) (λ _ _ → refl)

rec2ConstRight : ∀ {ℓz ℓw} {Z : Type ℓz} {W : Type ℓw}
  → (setZ : isSet Z)
  → (f : X → Z)
  → (x : ∥ X ∥₂)
  → (w : ∥ W ∥₂)
  → ST.rec2 setZ (λ x w → f x) x w ≡ ST.rec setZ f x
rec2ConstRight setZ f = ST.elim2 (λ _ _ → isSetSetPathImplicit setZ) (λ _ _ → refl)

map2ConstLeft : ∀ {ℓz ℓw} {Z : Type ℓz} {W : Type ℓw}
  → (f : W → Z)
  → (x : ∥ X ∥₂)
  → (w : ∥ W ∥₂)
  → map2 (λ x w → f w) x w ≡ ST.map f w
map2ConstLeft f = rec2ConstLeft ST.isSetSetTrunc (∣_∣₂ ∘ f)

map2IdRight : ∀ {ℓw} {W : Type ℓw}
  → (x : ∥ X ∥₂)
  → (w : ∥ W ∥₂)
  → map2 (λ x w → x) x w ≡ x
map2IdRight = ST.elim2 (λ _ _ → ST.isSetPathImplicit) (λ _ _ → refl)

setTruncIso : {A : Type ℓ} {B : Type ℓ'}
  → Iso A B
  → Iso ∥ A ∥₂ ∥ B ∥₂
setTruncIso {A = A} {B = B} isom = ∥isom∥ where
  open Iso

  ∥isom∥ : Iso _ _
  fun ∥isom∥ = ST.map (isom .fun)
  inv ∥isom∥ = ST.map (isom .inv)
  rightInv ∥isom∥ = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _)) (cong ∣_∣₂ ∘ isom .rightInv)
  leftInv ∥isom∥ = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _)) (cong ∣_∣₂ ∘ isom .leftInv)

setTruncEquiv : {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B
  → ∥ A ∥₂ ≃ ∥ B ∥₂
setTruncEquiv {A = A} {B = B} e = isoToEquiv (setTruncIso (equivToIso e))
