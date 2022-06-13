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

import Multiset.FiniteChoice as FiniteChoice

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
  renaming
    ( ∥_∥₁ to ∥_∥
    ; ∣_∣₁ to ∣_∣
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

-- Idempotency of 𝕄S on set truncations:

𝕄S∘∥-∥₂→𝕄S : 𝕄S ∥ X ∥₂ → 𝕄S X
𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = SQ.rec (OverSet.isSetFMSet) go well-defined v where
  open FiniteChoice

  -- TODO: Pull the n outside.
  go : (Fin n → ∥ X ∥₂) → 𝕄S X
  go = elimₙ {B = λ _ → 𝕄S X} (λ _ → OverSet.isSetFMSet) λ v → n , [ v ]₂

  well-defined : ∀ v w → SymmetricAction n v w → go v ≡ go w
  well-defined = elimₙ {B = λ v → (w : Fin n → ∥ X ∥₂) → SymmetricAction n v w → go v ≡ go w}
    {!   !}
    λ v → elimₙ {B = λ w → SymmetricAction n (λ k → ∣ v k ∣₂) w → go (λ k → ∣ v k ∣₂) ≡ go w}
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
  (FiniteChoice.elimₙ-comp {B = λ _ → 𝕄S X} (λ _ → OverSet.isSetFMSet) (λ v → n , [ v ]₂))
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
