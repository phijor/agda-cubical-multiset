{-# OPTIONS --safe #-}

module Multiset.FiniteChoice where

open import Multiset.Util using (Π⊥≡elim ; isPropΠ⊥)
import Multiset.Util.SetTruncation as STExt

open STExt using (∣_∣₂∗)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport
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
    X X' : Type ℓ
    n : ℕ
    Y : Fin n → Type ℓ'

open Iso

private
  -- Cons for Fin-indexed vectors:
  _∷_ : {Y : Fin (suc n) → Type ℓ'}
    → (Y fzero)
    → ((k : Fin n) → Y (fsuc k))
    → ((k : Fin (suc n)) → Y k)
  v₀ ∷ vₙ = Sum.elim (const v₀) vₙ

  -- Accessing the kᵗʰ element of a Fin-indexed vector.
  -- The partial application (at k) is a useful shorthand.
  at : (k : Fin n) → (v : (k : Fin n) → Y k) → Y k
  at k v = v k

module _ {Y : Fin (suc n) → Type ℓ'} where
  box-cons
    : ∥ Y fzero ∥₂
    → ∥ ((k : Fin n) → Y (fsuc k)) ∥₂
    → ∥ ((k : Fin (suc n)) → Y k) ∥₂
  box-cons = STExt.map2 _∷_

  box-cons-compute : {v : (k : Fin (suc n)) → Y k}
    → box-cons ∣ v fzero ∣₂ ∣ v ∘ fsuc ∣₂ ≡ ∣ v ∣₂
  box-cons-compute = cong ∣_∣₂ (funExt (Sum.elim (λ _ → refl) (λ _ → refl)))

module _ where
  box : ∀ {n} {Y : Fin n → Type ℓ'}
    → ((k : Fin n) → ∥ Y k ∥₂)
    → ∥ ((k : Fin n) → Y k) ∥₂
  box {n = ℕ.zero} v = ∣ ⊥.elim ∣₂
  box {n = suc n} {Y = Y} v = box-cons (v fzero) (box (v ∘ fsuc))

  box-compute : ∀ {n} {Y : Fin n → Type ℓ'}
    → (v : (k : Fin n) → Y k)
    → box (∣ v ∣₂∗) ≡ ∣ v ∣₂
  box-compute {n = 0} v = cong ∣_∣₂ (isPropΠ⊥ ⊥.elim v)
  box-compute {n = suc n} {Y = Y} v = goal where
    v₀ : Y fzero
    v₀ = v fzero

    vₙ : (k : Fin n) → Y (fsuc k)
    vₙ = v ∘ fsuc

    induction : box (∣_∣₂ ∘ vₙ) ≡ ∣ vₙ ∣₂
    induction = box-compute vₙ

    goal : box (∣_∣₂ ∘ v) ≡ ∣ v ∣₂
    goal =
      box-cons (∣ v₀ ∣₂) (box (∣_∣₂ ∘ vₙ))
        ≡⟨ cong (box-cons ∣ v₀ ∣₂) induction ⟩
      box-cons ∣ v₀ ∣₂ ∣ vₙ ∣₂
        ≡⟨ box-cons-compute ⟩
      ∣ v ∣₂
        ∎

unbox : ∥ ((k : Fin n) → Y k) ∥₂
  → (k : Fin n) → ∥ Y k ∥₂
unbox ∣v∣ k = ST.map (at k) ∣v∣

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

  -- First, we unfold the definitions of unbox and box once:
  unfold-once : ∀ k → unbox (box v) k ≡ STExt.map2 (λ y₀ yₙ → at {Y = Y} k (y₀ ∷ yₙ)) v₀ (box vₙ)
  unfold-once k =
    -- Both unbox and box are defined using map and map2, respectively.
    ST.map (at {Y = Y} k) (STExt.map2 _∷_ v₀ (box vₙ))
      ≡⟨
        -- Functoriality of set truncation means we can merge the above
        -- applications of map and map2 into a single application of map2:
        STExt.map∘map2 (at k) _ v₀ (box vₙ)
      ⟩
    STExt.map2 (λ y₀ yₙ → at {Y = Y} k (y₀ ∷ yₙ)) v₀ (box vₙ)
      ∎

  case₀ : unbox (box v) fzero ≡ v fzero
  case₀ =
    unbox (box v) fzero
      ≡⟨ -- Unfold the definitions once.
        unfold-once fzero
      ⟩
    STExt.map2 (λ y₀ yₙ → at {Y = Y} fzero (y₀ ∷ yₙ)) v₀ (box vₙ)
      ≡⟨ -- Accessing the cons of a head (y₀) and a tail (yₙ) at
         -- index 0 is constant in the tail and simply returns the head.
        STExt.map2IdRight v₀ (box vₙ)
      ⟩
    v₀
      ∎

  caseₙ : (k : Fin n) → unbox (box v) (fsuc k) ≡ v (fsuc k)
  caseₙ k =
    unbox (box v) (fsuc k)
      ≡⟨ {- Unfold defs -} unfold-once (fsuc k) ⟩
    STExt.map2 (λ y₀ yₙ → at k yₙ) v₀ (box vₙ)
      ≡⟨ -- Accessing the cons of a head (y₀) and a tail (yₙ) at
         -- a index (k + 1) is constant in the head and reduces
         -- to accessing the tail at index k.
        STExt.map2ConstLeft _ v₀ (box vₙ)
      ⟩
    ST.map (at k) (box vₙ)
      ≡⟨ {- Notice that this is just the goal again, but at k + 1. -} refl ⟩
    unbox (box {Y = Y ∘ fsuc} vₙ) k
      ≡⟨ -- By induction, this reduces to the tail at index k
        funExt⁻ (unbox∘box {n = n} vₙ) k
      ⟩
    vₙ k
      ∎

unbox∘box-compute : ∀ {n : ℕ} {Y : Fin n → Type ℓ'} {v : (k : Fin n) → Y k}
  → unbox∘box ∣ v ∣₂∗ ≡ cong unbox (box-compute v)
unbox∘box-compute = isSetΠ (λ _ → ST.isSetSetTrunc) _ _ _ _

box∘unbox : (v : ∥ ((k : Fin n) → Y k) ∥₂)
  → box (unbox v) ≡ v
box∘unbox = ST.elim (λ _ → ST.isSetPathImplicit) box-compute

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

module _ {B : (Fin n → ∥ X ∥₂) → Type ℓ'}
  (setB : ∀ ∣v∣ → isSet (B ∣v∣))
  (choice : (v : Fin n → X) → B (λ k → ∣ v k ∣₂)) where

  elimₙ′ : (v : Fin n → ∥ X ∥₂) → B (unbox (box v))
  elimₙ′ v = ST.elim {B = B ∘ unbox} (setB ∘ unbox) choice (box v)

  elimₙ : (v : Fin n → ∥ X ∥₂) → B v
  elimₙ v = subst B (unbox∘box v) (elimₙ′ v)

  elimₙ′-comp : (v : Fin n → X)
    → PathP (λ i → B (unbox (box-compute v i)))
      (elimₙ′ ∣ v ∣₂∗)
      (choice v)
  elimₙ′-comp v = cong (ST.elim (setB ∘ unbox) choice) (box-compute v)

  elimₙ′-comp′ : (v : Fin n → X)
    → PathP (λ i → B (unbox∘box ∣ v ∣₂∗ i))
      (elimₙ′ ∣ v ∣₂∗)
      (choice v)
  elimₙ′-comp′ v = subst (λ p → PathP (λ i → B (p i)) (elimₙ′ ∣ v ∣₂∗) (choice v)) (sym unbox∘box-compute) (elimₙ′-comp v)

  elimₙ-comp : (v : Fin n → X) → elimₙ ∣ v ∣₂∗ ≡ choice v
  elimₙ-comp v =
    subst B (unbox∘box ∣ v ∣₂∗) (ST.elim (setB ∘ unbox) choice (box (∣ v ∣₂∗)))
      ≡⟨ fromPathP (elimₙ′-comp′ v) ⟩
    ST.elim (setB ∘ unbox) choice ∣ v ∣₂
      ≡⟨⟩
    choice v
      ∎

elim2ₙ : {B : (v : Fin n → ∥ X ∥₂) (v : Fin n → ∥ X' ∥₂) → Type ℓ'}
  → (setB : ∀ ∣v∣ ∣w∣ → isSet (B ∣v∣ ∣w∣))
  → (choice : (v : Fin n → X) (w : Fin n → X') → B ∣ v ∣₂∗ ∣ w ∣₂∗)
  → (v : Fin n → ∥ X ∥₂) (w : Fin n → ∥ X' ∥₂) → B v w
elim2ₙ {n = n} {X' = X'} {B = B} setB choice =
  elimₙ {B = λ v → (w : Fin n → ∥ X' ∥₂) → B v w}
    (λ ∣v∣ → isSetΠ (λ ∣w∣ → setB ∣v∣ ∣w∣))
    (λ v → elimₙ
      (λ ∣w∣ → setB ∣ v ∣₂∗ ∣w∣)
      (λ w → choice v w)
    )

recₙ : {A : Type ℓ'}
  → (setA : isSet A)
  → (choice : (Fin n → X) → A)
  → (Fin n → ∥ X ∥₂) → A
recₙ setA = elimₙ (λ _ → setA)

rec2ₙ : {A : Type ℓ'}
  → (setA : isSet A)
  → (choice : (v w : Fin n → X) → A)
  → (v w : Fin n → ∥ X ∥₂) → A
rec2ₙ setA = elim2ₙ (λ _ _ → setA)


open import Cubical.HITs.PropositionalTruncation as PT

module _ {Y : Fin (suc n) → Type ℓ'} where
  box-cons₁
    : ∥ Y fzero ∥₁
    → ∥ ((k : Fin n) → Y (fsuc k)) ∥₁
    → ∥ ((k : Fin (suc n)) → Y k) ∥₁
  box-cons₁ = PT.map2 _∷_

module _ where
  box₁ : ∀ {n} {Y : Fin n → Type ℓ'}
    → ((k : Fin n) → ∥ Y k ∥₁)
    → ∥ ((k : Fin n) → Y k) ∥₁
  box₁ {n = ℕ.zero} v = ∣ ⊥.elim ∣₁
  box₁ {n = suc n} {Y = Y} v = box-cons₁ (v fzero) (box₁ (v ∘ fsuc))

unbox₁ : ∥ ((k : Fin n) → Y k) ∥₁
  → (k : Fin n) → ∥ Y k ∥₁
unbox₁ ∣v∣ k = PT.map (at k) ∣v∣
