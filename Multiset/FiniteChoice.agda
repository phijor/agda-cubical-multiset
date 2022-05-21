module Multiset.FiniteChoice where

open import Multiset.Util using (Π⊥≡elim ; isPropΠ⊥)
import Multiset.Util.SetTruncation as STExt

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
  using
    ( isSet-subst
    )
open import Cubical.Foundations.Isomorphism
  using
    ( Iso
    ; isoToEquiv
    ; iso
    )
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using
    ( _∘_
    ; const
    )

open import Cubical.Data.Empty as ⊥
  using
    ( ⊥
    )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    ; _+_
    )
open import Cubical.Data.SumFin as Fin

open import Cubical.HITs.SetTruncation as ST
  using
    ( ∥_∥₂
    ; ∣_∣₂
    )

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ
    n : ℕ
    Y : Fin n → Type ℓ'

open Iso

module _ {Y : Fin (suc n) → Type ℓ'} where
  box-cons
    : ∥ Y fzero ∥₂
    → ∥ ((k : Fin n) → Y (fsuc k)) ∥₂
    → ∥ ((k : Fin (suc n)) → Y k) ∥₂
  box-cons = STExt.map2 (λ v₀ vₙ → Sum.elim (const v₀) vₙ)

  box-cons-up : {v : (k : Fin (suc n)) → Y k}
    → box-cons ∣ v fzero ∣₂ ∣ v ∘ fsuc ∣₂ ≡ ∣ v ∣₂
  box-cons-up = cong ∣_∣₂ (funExt (Sum.elim (λ _ → refl) (λ _ → refl)))

module _ where
  box : ∀ {n} {Y : Fin n → Type ℓ'}
    → ((k : Fin n) → ∥ Y k ∥₂)
    → ∥ ((k : Fin n) → Y k) ∥₂
  box {n = ℕ.zero} v = ∣ ⊥.elim ∣₂
  box {n = suc n} {Y = Y} v = box-cons (v fzero) (box (v ∘ fsuc))

  box-up : ∀ {n} {Y : Fin n → Type ℓ'}
    → (v : (k : Fin n) → Y k)
    → box (∣_∣₂ ∘ v) ≡ ∣ v ∣₂
  box-up {n = 0} v = cong ∣_∣₂ (isPropΠ⊥ ⊥.elim v)
  box-up {n = suc n} {Y = Y} v = goal where
    v₀ : Y fzero
    v₀ = v fzero

    vₙ : (k : Fin n) → Y (fsuc k)
    vₙ = v ∘ fsuc

    induction : box (∣_∣₂ ∘ vₙ) ≡ ∣ vₙ ∣₂
    induction = box-up vₙ

    goal : box (∣_∣₂ ∘ v) ≡ ∣ v ∣₂
    goal =
      box-cons (∣ v₀ ∣₂) (box (∣_∣₂ ∘ vₙ))
        ≡⟨ cong (box-cons ∣ v₀ ∣₂) induction ⟩
      box-cons ∣ v₀ ∣₂ ∣ vₙ ∣₂
        ≡⟨ box-cons-up ⟩
      ∣ v ∣₂
        ∎

unbox : ∥ ((k : Fin n) → Y k) ∥₂
  → (k : Fin n) → ∥ Y k ∥₂
unbox ∣v∣ k = ST.map (λ v → v k) ∣v∣

unbox∘box : ∀ {n : ℕ} {Y : Fin n → Type ℓ'}
  → (v : (k : Fin n) → ∥ Y k ∥₂)
  → unbox (box v) ≡ v
unbox∘box {n = 0} v = isPropΠ⊥ _ v
unbox∘box {n = suc n} {Y = Y} v = funExt (Sum.elim (λ (_ : ⊤) → case₀) caseₙ) where
  -- v is a vector of length 1 + n:
  _ : (k : Fin (1 + n)) → ∥ Y k ∥₂
  _ = v

  -- Denote its head by v₀:
  v₀ : ∥ Y fzero ∥₂
  v₀ = v fzero

  -- ...and its n elements long tail by vₙ:
  vₙ : (k : Fin n) → ∥ Y (fsuc k) ∥₂
  vₙ = v ∘ fsuc

  ∣vₙ∣ : ∥ ((k : Fin n) → Y (fsuc k)) ∥₂
  ∣vₙ∣ = box {Y = Y ∘ fsuc} (v ∘ fsuc)

  case₀ : unbox (box v) fzero ≡ v fzero
  case₀ =
    unbox (box v) fzero
      ≡⟨ STExt.mapMap2 _ (λ v → v fzero) v₀ ∣vₙ∣ ⟩
    STExt.map2 (λ y₀ _ → y₀) v₀ ∣vₙ∣
      ≡⟨ STExt.map2IdRight v₀ ∣vₙ∣ ⟩
    v fzero
      ∎

  caseₙ : (k : Fin n) → unbox (box v) (fsuc k) ≡ v (fsuc k)
  caseₙ k =
    unbox (box v) (fsuc k)
      ≡⟨ STExt.mapMap2 _ (λ v → v (fsuc k)) v₀ ∣vₙ∣ ⟩
    STExt.map2 (λ _ v → v k) v₀ ∣vₙ∣
      ≡⟨ STExt.map2ConstLeft _ v₀ ∣vₙ∣ ⟩
    ST.map (λ v → v k) ∣vₙ∣
      ≡⟨ refl ⟩
    unbox (box {Y = Y ∘ fsuc} vₙ) k
      ≡⟨ funExt⁻ (unbox∘box {n = n} vₙ) k ⟩
    vₙ k
      ∎

box∘unbox : (v : ∥ ((k : Fin n) → Y k) ∥₂)
  → box (unbox v) ≡ v
box∘unbox = ST.elim (λ _ → ST.isSetPathImplicit) box-up

setFinChoice≅ : (Y : Fin n → Type ℓ')
  → Iso ((k : Fin n) → ∥ Y k ∥₂) ∥ ((k : Fin n) → Y k) ∥₂
setFinChoice≅ Y = go where
  go : Iso _ _
  go .fun = box
  go .inv = unbox
  go .rightInv = box∘unbox
  go .leftInv = unbox∘box

setFinChoice≃ : (Y : Fin n → Type ℓ')
  → ((k : Fin n) → ∥ Y k ∥₂) ≃ ∥ ((k : Fin n) → Y k) ∥₂
setFinChoice≃ Y = isoToEquiv (setFinChoice≅ Y)


elimₙ : ∀ {B : (Fin n → ∥ X ∥₂) → Type ℓ'}
  → (setB : ∀ ∣v∣ → isSet (B ∣v∣))
  → (choice : (v : Fin n → X) → B (λ k → ∣ v k ∣₂))
  → (v : Fin n → ∥ X ∥₂) → B v
elimₙ {B = B} setB choice v = goal where
  step : B (unbox (box v))
  step = ST.elim {B = B ∘ unbox} (setB ∘ unbox) choice (box v)

  goal : B v
  goal = subst B (unbox∘box v) step

elimₙ-comp : ∀ {n : ℕ} {B : (Fin n → ∥ X ∥₂) → Type ℓ'}
  → (setB : ∀ ∣v∣ → isSet (B ∣v∣))
  → (choice : (v : Fin n → X) → B (λ k → ∣ v k ∣₂))
  → (v : Fin n → X) → elimₙ setB choice (∣_∣₂ ∘ v) ≡ choice v
elimₙ-comp {X = X} {B = B} setB choice v = let Q = isSet-subst {B = B} (isSetΠ (λ _ → ST.isSetSetTrunc)) (unbox∘box {!   !}) in {!   !}
