module Multiset.Equiv where

open import Multiset.OverSet as OverSet
  using
    ( SymmetricAction
    ; _∼_
    )
  renaming
    ( FMSet to 𝕄S
    )

open import Multiset.OverGroupoid as OverGroupoid
  using ()
  renaming
    ( FMSet to 𝕄G
    )

open import Multiset.Util using (Π⊥≡elim ; isPropΠ⊥)
import Multiset.Util.SetTruncation as STExt

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
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

open import Cubical.Data.Unit as ⊤
  using
    ( Unit
    )
open import Cubical.Data.Empty as ⊥
  using
    ( ⊥
    )
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )
open import Cubical.Data.Sigma as Σ
  using
    ( _×_
    ; ΣPathP
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    ; _+_
    )
open import Cubical.Data.FinSet as FinSet
  using
    ( FinSet
    ; isFinSet
    ; isFinSetFin
    ; isPropIsFinSet
    )
open import Cubical.Data.SumFin as Fin

open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming
    ( _/_ to _/₂_
    ; [_] to [_]₂
    )
open import Cubical.HITs.SetTruncation as ST
  using
    ( ∥_∥₂
    ; ∣_∣₂
    ; squash₂
    ; isSetSetTrunc
    )
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∥_∥
    ; ∣_∣
    )

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

open Iso

𝕄S→∥𝕄G∥₂ : 𝕄S X → ∥ 𝕄G X ∥₂
𝕄S→∥𝕄G∥₂ (n , x) = SQ.rec squash₂ f well-defined x where
  f : (Fin n → X) → ∥ 𝕄G X ∥₂
  f v = ∣ (Fin n , isFinSetFin) , v ∣₂

  well-defined : (v w : Fin n → X) → OverSet.SymmetricAction n v w → f v ≡ f w
  well-defined v w (σ , v∘σ≡w) = cong ∣_∣₂ (OverGroupoid.FMSetPath (ua σ) v∘σ≡w)

𝕄G→𝕄S : 𝕄G X → 𝕄S X
𝕄G→𝕄S {X = X} ((Y , n , e) , v) = n , (PT.rec→Set SQ.squash/ from-equiv is2Const e) where
  from-equiv : Y ≃ Fin n → (Fin n → X) /₂ SymmetricAction n
  from-equiv α = [ v ∘ invEq α ]₂

  is2Const : (α β : Y ≃ Fin n) → [ v ∘ (invEq α) ]₂ ≡ [ v ∘ (invEq β) ]₂
  is2Const α β = SQ.eq/ {R = SymmetricAction n} _ _ (σ , ua→ step₂) where
    σ : Fin n ≃ Fin n
    σ = invEquiv α ∙ₑ β

    α⁻ = invEq α
    β⁺ = equivFun β
    β⁻ = invEq β

    module _ (k : Fin n) where
      step₁ : α⁻ k ≡ β⁻ (β⁺ (α⁻ k))
      step₁ = sym (retEq β (α⁻ k))

      step₂ : v (α⁻ k) ≡ v (β⁻ (β⁺ (α⁻ k)))
      step₂ = cong v step₁

∥𝕄G∥₂→𝕄S : ∥ 𝕄G X ∥₂ → 𝕄S X
∥𝕄G∥₂→𝕄S = ST.rec OverSet.isSetFMSet 𝕄G→𝕄S

-- Section
∥𝕄G∥₂→𝕄S→∥𝕄G∥₂ : (x : ∥ 𝕄G X ∥₂) → 𝕄S→∥𝕄G∥₂ (∥𝕄G∥₂→𝕄S x) ≡ x
∥𝕄G∥₂→𝕄S→∥𝕄G∥₂ {X = X} = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _)) go where

  module _ (Y : Type) (n : ℕ) (v : Y → X) (α : Y ≃ Fin n) where
    equiv-path :
      (λ i → ∥ ua (invEquiv α) i ≃ Fin n ∥) [ ∣ idEquiv (Fin n) ∣ ≡ ∣ α ∣ ]
    equiv-path = isProp→PathP (λ i → PT.isPropPropTrunc) _ _

    is-permutation : ∀ k → (v ∘ invEq α) k ≡ v (invEq α k)
    is-permutation _ = refl

    sect : ∣ (Fin n , n , ∣ idEquiv (Fin n) ∣) , v ∘ invEq α ∣₂ ≡ ∣ (Y , n , ∣ α ∣) , v ∣₂
    sect = cong ∣_∣₂ (OverGroupoid.FMSetPathP≃ (invEquiv α) is-permutation)

  f : ∥ 𝕄G X ∥₂ → ∥ 𝕄G X ∥₂
  f x = 𝕄S→∥𝕄G∥₂ (∥𝕄G∥₂→𝕄S x)

  -- Proof by induction on the propositionally truncated
  -- equivalence (e : ∥ Y ≃ Fin k ∥):
  go : (x : 𝕄G X) → f ∣ x ∣₂ ≡ ∣ x ∣₂
  go ((Y , n , e) , v) = PT.elim
    -- Equality in a set truncation is a proposition:
    (λ α → let x = ∣ (Y , n , α) , v ∣₂ in squash₂ (f x) x)
    (sect Y n v)
    e

𝕄S→∥𝕄G∥₂→𝕄S : (x : 𝕄S X) → ∥𝕄G∥₂→𝕄S (𝕄S→∥𝕄G∥₂ x) ≡ x
𝕄S→∥𝕄G∥₂→𝕄S (n , v) = SQ.elimProp
  {P = λ v → ∥𝕄G∥₂→𝕄S (𝕄S→∥𝕄G∥₂ (n , v)) ≡ (n , v)}
  (λ _ → OverSet.isSetFMSet _ _)
  (λ v → refl)
  v

𝕄S≃∥𝕄G∥₂ : 𝕄S X ≃ ∥ 𝕄G X ∥₂
𝕄S≃∥𝕄G∥₂ = isoToEquiv (iso 𝕄S→∥𝕄G∥₂ ∥𝕄G∥₂→𝕄S ∥𝕄G∥₂→𝕄S→∥𝕄G∥₂ 𝕄S→∥𝕄G∥₂→𝕄S)

module Choice where
  box-cons : {n : ℕ}
    → {Y : Fin (suc n) → Type ℓ'}
    → ∥ Y fzero ∥₂
    → ∥ ((k : Fin n) → Y (fsuc k)) ∥₂
    → ∥ ((k : Fin (suc n)) → Y k) ∥₂
  box-cons = STExt.map2 (λ v₀ vₙ → Sum.elim (const v₀) vₙ)

  box-cons-up : {n : ℕ}
    → {Y : Fin (suc n) → Type ℓ'}
    → {v : (k : Fin (suc n)) → Y k}
    → box-cons {Y = Y} ∣ v fzero ∣₂ ∣ v ∘ fsuc ∣₂ ≡ ∣ v ∣₂
  box-cons-up = cong ∣_∣₂ (funExt (Sum.elim (λ _ → refl) (λ _ → refl)))

  box : {n : ℕ}
    → {Y : Fin n → Type ℓ'}
    → ((k : Fin n) → ∥ Y k ∥₂) →  ∥ ((k : Fin n) → Y k) ∥₂
  box {n = ℕ.zero} v = ∣ ⊥.elim ∣₂
  box {n = suc n} {Y = Y} v = box-cons (v fzero) (box (v ∘ inr))

  box-up : {n : ℕ}
    → {Y : Fin n → Type ℓ'}
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

  unbox : {n : ℕ}
    → {Y : Fin n → Type ℓ'}
    → ∥ ((k : Fin n) → Y k) ∥₂ → (k : Fin n) → ∥ Y k ∥₂
  unbox ∣v∣ k = ST.map (λ v → v k) ∣v∣

  unbox∘box : ∀ {n : ℕ} {Y : Fin n → Type ℓ'} (v : (k : Fin n) → ∥ Y k ∥₂)
    → unbox (box v) ≡ v
  unbox∘box {n = 0} v = isContr→isProp ⊥.isContrΠ⊥ _ v
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

  box∘unbox : ∀ {n : ℕ} {Y : Fin n → Type ℓ'} (v : ∥ ((k : Fin n) → Y k) ∥₂)
    → box (unbox v) ≡ v
  box∘unbox = ST.elim (λ _ → ST.isSetPathImplicit) box-up

  setChoice≅Fin : {n : ℕ}
    → (Y : Fin n → Type ℓ')
    → Iso ((k : Fin n) → ∥ Y k ∥₂) ∥ ((k : Fin n) → Y k) ∥₂
  setChoice≅Fin Y = go where
    go : Iso _ _
    go .fun = box
    go .inv = unbox
    go .rightInv = box∘unbox
    go .leftInv = unbox∘box

  setChoice≃Fin : {n : ℕ}
    → (Y : Fin n → Type ℓ')
    → ((k : Fin n) → ∥ Y k ∥₂) ≃ ∥ ((k : Fin n) → Y k) ∥₂
  setChoice≃Fin Y = isoToEquiv (setChoice≅Fin Y)


  elimₙ : ∀ {n} {P : (Fin n → ∥ X ∥₂) → Type ℓ'}
    → (setP : ∀ ∣v∣ → isSet (P ∣v∣))
    → (choice : (v : Fin n → X) → P (λ k → ∣ v k ∣₂))
    → (v : Fin n → ∥ X ∥₂) → P v
  elimₙ {P = P} setP choice v = goal where
    step : P (unbox (box v))
    step = ST.elim {B = P ∘ unbox} (setP ∘ unbox) choice (box v)

    goal : P v
    goal = subst P (unbox∘box v) step

  elimₙ-comp : ∀ {n} {P : (Fin n → ∥ X ∥₂) → Type ℓ'}
    → (setP : ∀ ∣v∣ → isSet (P ∣v∣))
    → (choice : (v : Fin n → X) → P (λ k → ∣ v k ∣₂))
    → (v : Fin n → X) → elimₙ setP choice (∣_∣₂ ∘ v) ≡ choice v
  elimₙ-comp setP choice v = {!   !}

-- Idempotency of 𝕄S on set truncations:

𝕄S∘∥-∥₂→𝕄S : 𝕄S ∥ X ∥₂ → 𝕄S X
𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = SQ.rec (OverSet.isSetFMSet) go well-defined v where
  open Choice

  -- TODO: Pull the n outside.
  go : (Fin n → ∥ X ∥₂) → 𝕄S X
  go = Choice.elimₙ {P = λ _ → 𝕄S X} (λ _ → OverSet.isSetFMSet) λ v → n , [ v ]₂

  well-defined : ∀ v w → SymmetricAction n v w → go v ≡ go w
  well-defined = elimₙ {P = λ v → (w : Fin n → ∥ X ∥₂) → SymmetricAction n v w → go v ≡ go w}
    {!   !}
    λ v → elimₙ {P = λ w → SymmetricAction n (λ k → ∣ v k ∣₂) w → go (λ k → ∣ v k ∣₂) ≡ go w}
      {!   !}
      λ w (σ , p) →
        elimₙ-comp (λ _ → OverSet.isSetFMSet) (λ v → n , [ v ]₂) v
          ∙ OverSet.FMSetPath v w σ (ua→ {! ua→⁻ p  !}) -- TODO: Need to proptrunc the witness `p` in def of SymmetricAction
          ∙ sym (elimₙ-comp (λ _ → OverSet.isSetFMSet) (λ v → n , [ v ]₂) w)

𝕄S→𝕄S∘∥-∥₂ : 𝕄S X → 𝕄S ∥ X ∥₂
𝕄S→𝕄S∘∥-∥₂ (n , [v]) = n , SQ.rec SQ.squash/ go well-defined [v] where
  box : (Fin n → X) → (Fin n → ∥ X ∥₂)
  box v = ∣_∣₂ ∘ v

  go : (Fin n → X) → (Fin n → ∥ X ∥₂) /₂ SymmetricAction n
  go v = [ box v ]₂

  module _ (v w : Fin n → X) (v∼w : v ∼ w) where
    well-defined : go v ≡ go w
    well-defined = SQ.eq/ (box v) (box w) (OverSet.∼cong ∣_∣₂ v∼w)

𝕄S→𝕄S∘∥-∥₂→𝕄S : (xs : 𝕄S X) → 𝕄S∘∥-∥₂→𝕄S (𝕄S→𝕄S∘∥-∥₂ xs) ≡ xs
𝕄S→𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = SQ.elimProp {P = λ v → 𝕄S∘∥-∥₂→𝕄S (𝕄S→𝕄S∘∥-∥₂ (n , v)) ≡ (n , v)}
  (λ _ → OverSet.isSetFMSet _ _)
  (Choice.elimₙ-comp {P = λ _ → 𝕄S X} (λ _ → OverSet.isSetFMSet) (λ v → n , [ v ]₂))
  v

𝕄S∘∥-∥₂≃𝕄S : 𝕄S ∥ X ∥₂ ≃ 𝕄S X
𝕄S∘∥-∥₂≃𝕄S = isoToEquiv (iso 𝕄S∘∥-∥₂→𝕄S 𝕄S→𝕄S∘∥-∥₂ {!   !} {!   !})

module HIT where
  open import Cubical.HITs.FiniteMultiset as FMSet
    using
      ( FMSet
      ; _∷_
      ; []
      ; [_]
      )

  ∣_∣₂∷_ :  X → FMSet ∥ X ∥₂ → FMSet ∥ X ∥₂
  ∣ x ∣₂∷ xs = ∣ x ∣₂ ∷ xs

  ∣∣₂∷-comm : (x y : X) → (xs : FMSet ∥ X ∥₂) → ∣ x ∣₂ ∷ ∣ y ∣₂ ∷ xs ≡ ∣ y ∣₂ ∷ ∣ x ∣₂ ∷ xs
  ∣∣₂∷-comm x y xs = FMSet.comm ∣ x ∣₂ ∣ y ∣₂ xs

  FMSet→FMSet∥∥₂ : FMSet X → FMSet ∥ X ∥₂
  FMSet→FMSet∥∥₂ = FMSet.Rec.f FMSet.trunc [] ∣_∣₂∷_ ∣∣₂∷-comm

  _∷*_ : ∥ X ∥₂ → FMSet X → FMSet X
  _∷*_ = ST.rec (isSetΠ (λ _ → FMSet.trunc)) _∷_

  ∷*-comm : (x y : ∥ X ∥₂) → (xs : FMSet X) → x ∷* (y ∷* xs) ≡ y ∷* (x ∷* xs)
  ∷*-comm ∣x∣ ∣y∣ xs = ST.elim2 {C = λ ∣x∣ ∣y∣ → ∣x∣ ∷* (∣y∣ ∷* xs) ≡ ∣y∣ ∷* (∣x∣ ∷* xs)}
    (λ _ _ → isProp→isSet (FMSet.trunc _ _))
    (λ x y → FMSet.comm x y xs) ∣x∣ ∣y∣

  FMSet∥∥₂→FMSet : FMSet ∥ X ∥₂ → FMSet X
  FMSet∥∥₂→FMSet = FMSet.Rec.f FMSet.trunc [] _∷*_ ∷*-comm

  FMSet≅FMSet∥∥₂ : Iso (FMSet X) (FMSet ∥ X ∥₂)
  FMSet≅FMSet∥∥₂ .fun = FMSet→FMSet∥∥₂
  FMSet≅FMSet∥∥₂ .inv = FMSet∥∥₂→FMSet
  FMSet≅FMSet∥∥₂ {X = X} .rightInv =
    FMSet.ElimProp.f (FMSet.trunc _ _) refl lemma where
      lemma : (∣x∣ : ∥ X ∥₂)
        → {xs : FMSet ∥ X ∥₂}
        → FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet xs) ≡ xs
        → FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet (∣x∣ ∷ xs)) ≡ ∣x∣ ∷ xs
      lemma = ST.elim
        {B = λ ∣x∣ → ∀ {xs} → (FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet xs) ≡ xs) → FMSet→FMSet∥∥₂ (FMSet∥∥₂→FMSet (∣x∣ ∷ xs)) ≡ ∣x∣ ∷ xs}
        (λ ∣x∣ → isSetImplicitΠ λ xs → isSetΠ λ p → isProp→isSet (FMSet.trunc _ _))
        (λ x → cong ∣ x ∣₂∷_)
  FMSet≅FMSet∥∥₂ .leftInv = FMSet.ElimProp.f (FMSet.trunc _ _) (refl {x = []}) λ x → cong (x ∷_)

  FMSet≃FMSet∥∥₂ : FMSet X ≃ FMSet ∥ X ∥₂
  FMSet≃FMSet∥∥₂ = isoToEquiv FMSet≅FMSet∥∥₂
