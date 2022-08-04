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

open import Multiset.Util using (Π⊥≡elim ; isPropΠ⊥ ; ua→cong ; ua→PathP)
import Multiset.Util.SetTruncation as STExt
open STExt using (∣_∣₂∗)

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
    )

open import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma as Σ
  using
    ( ΣPathP
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
open import Cubical.Data.FinSet.FiniteChoice as FinSet
  using (choice≃Fin)
open import Cubical.Data.SumFin as Fin

open import Cubical.HITs.SetQuotients as SQ
  using ()
  renaming
    ( _/_ to _/₂_
    ; [_] to [_]₂
    ; eq/ to eq/₂
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
  well-defined v w = PT.elim
    (λ _ → isSetSetTrunc _ _)
    (λ (σ , v∘σ≡w) → cong ∣_∣₂ (OverGroupoid.FMSetPath (ua σ) v∘σ≡w))

𝕄G→𝕄S : 𝕄G X → 𝕄S X
𝕄G→𝕄S {X = X} ((Y , n , e) , v) = n , (PT.rec→Set SQ.squash/ from-equiv is2Const e) where
  from-equiv : Y ≃ Fin n → (Fin n → X) /₂ SymmetricAction n
  from-equiv α = [ v ∘ invEq α ]₂

  is2Const : (α β : Y ≃ Fin n) → [ v ∘ (invEq α) ]₂ ≡ [ v ∘ (invEq β) ]₂
  is2Const α β = SQ.eq/ {R = SymmetricAction n} _ _ ∣ σ , (ua→ step₂) ∣ where
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

𝕄S-∥𝕄G∥₂-Iso : Iso (𝕄S X) (∥ 𝕄G X ∥₂)
𝕄S-∥𝕄G∥₂-Iso .fun = 𝕄S→∥𝕄G∥₂
𝕄S-∥𝕄G∥₂-Iso .inv = ∥𝕄G∥₂→𝕄S
𝕄S-∥𝕄G∥₂-Iso .rightInv = ∥𝕄G∥₂→𝕄S→∥𝕄G∥₂
𝕄S-∥𝕄G∥₂-Iso .leftInv = 𝕄S→∥𝕄G∥₂→𝕄S

𝕄S≃∥𝕄G∥₂ : 𝕄S X ≃ ∥ 𝕄G X ∥₂
𝕄S≃∥𝕄G∥₂ = isoToEquiv 𝕄S-∥𝕄G∥₂-Iso

-- Idempotency of 𝕄S on set truncations:
requot : ∀ {n} → (Fin n → ∥ X ∥₂) → ((Fin n → X) /₂ SymmetricAction n)
requot {X = X} {n = n} = FiniteChoice.elimₙ {B = λ _ → (Fin n → X) /₂ SymmetricAction n} (λ _ → SQ.squash/) [_]₂

requot-comp : ∀ {n} → (v : Fin n → X) → requot ∣ v ∣₂∗ ≡ [ v ]₂
requot-comp {X = X} {n = n} = FiniteChoice.elimₙ-comp {B = λ _ → (Fin n → X) /₂ SymmetricAction n} (λ _ → SQ.squash/) [_]₂

𝕄S∘∥-∥₂→𝕄S : 𝕄S ∥ X ∥₂ → 𝕄S X
𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = n , SQ.rec (SQ.squash/) requot well-defined v where
  open FiniteChoice

  module _ {v w : Fin n → X} where
    module _ {σ : Fin n ≃ Fin n} (p : ua→PathP σ ∣ v ∣₂∗ ∣ w ∣₂∗) where
      mereEqPointwise : (k : Fin n) → ∥ v k ≡ w (equivFun σ k) ∥
      mereEqPointwise k = ST.PathIdTrunc₀Iso .fun (ua→⁻ p k)

      chosenEq : ∥ ((k : Fin n) → v k ≡ w (equivFun σ k)) ∥
      chosenEq = equivFun (choice≃Fin _) mereEqPointwise

      chosenPath : ∥ ua→PathP σ v w ∥
      chosenPath = PT.map ua→ chosenEq

    liftRel : (Σ[ σ ∈ Fin n ≃ Fin n ] ua→PathP σ ∣ v ∣₂∗ ∣ w ∣₂∗) → v ∼ w
    liftRel (σ , p) = PT.map (σ ,_) (chosenPath p)

    lift[_]₂ : ∣ v ∣₂∗ ∼ ∣ w ∣₂∗ → Path ((Fin n → X) /₂ SymmetricAction n) [ v ]₂ [ w ]₂
    lift[_]₂ v∼w = PT.rec (OverSet.isSetSymmQuot _ _) (eq/₂ v w ∘ liftRel) v∼w

  well-defined : ∀ v w → SymmetricAction n v w → requot v ≡ requot w
  well-defined = elim2ₙ (λ _ _ → isSetΠ (λ _ → isProp→isSet (OverSet.isSetSymmQuot _ _)))
    λ v w v∼w →
      requot ∣ v ∣₂∗ ≡⟨ requot-comp v ⟩
      [ v ]₂         ≡⟨ lift[ v∼w ]₂ ⟩
      [ w ]₂         ≡⟨ sym (requot-comp w) ⟩
      requot ∣ w ∣₂∗ ∎

𝕄S→𝕄S∘∥-∥₂ : 𝕄S X → 𝕄S ∥ X ∥₂
𝕄S→𝕄S∘∥-∥₂ (n , [v]) = n , SQ.rec SQ.squash/ go well-defined [v] where
  go : (Fin n → X) → (Fin n → ∥ X ∥₂) /₂ SymmetricAction n
  go v = [ ∣_∣₂ ∘ v ]₂

  module _ (v w : Fin n → X) (v∼w : v ∼ w) where
    well-defined : go v ≡ go w
    well-defined = SQ.eq/ (∣_∣₂ ∘ v) (∣_∣₂ ∘ w) (OverSet.∼cong ∣_∣₂ v∼w)

𝕄S→𝕄S∘∥-∥₂→𝕄S : (xs : 𝕄S X) → 𝕄S∘∥-∥₂→𝕄S (𝕄S→𝕄S∘∥-∥₂ xs) ≡ xs
𝕄S→𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = ΣPathP (refl , lemma) where
  lemma : (𝕄S∘∥-∥₂→𝕄S (𝕄S→𝕄S∘∥-∥₂ (n , v))) .snd ≡ v
  lemma = SQ.elimProp {P = λ v → 𝕄S∘∥-∥₂→𝕄S (𝕄S→𝕄S∘∥-∥₂ (n , v)) .snd ≡ v}
    (λ _ → SQ.squash/ _ _)
    (FiniteChoice.elimₙ-comp {B = λ _ → (Fin n → X) /₂ SymmetricAction n}
      (λ _ → SQ.squash/)
      [_]₂
    )
    v

𝕄S∘∥-∥₂→𝕄S→𝕄S∘∥-∥₂ : (xs : 𝕄S ∥ X ∥₂) → 𝕄S→𝕄S∘∥-∥₂ (𝕄S∘∥-∥₂→𝕄S xs) ≡ xs
𝕄S∘∥-∥₂→𝕄S→𝕄S∘∥-∥₂ {X = X} (n , v) = ΣPathP (refl , lemma) where
  step : (v : Fin n → ∥ X ∥₂) → 𝕄S→𝕄S∘∥-∥₂ (n , requot v) .snd ≡ [ v ]₂
  step = FiniteChoice.elimₙ {B = λ v → 𝕄S→𝕄S∘∥-∥₂ (n , requot v) .snd ≡ [ v ]₂}
    (λ _ → isProp→isSet (OverSet.isSetSymmQuot _ _))
    λ v →
      𝕄S→𝕄S∘∥-∥₂ (n , requot ∣ v ∣₂∗) .snd ≡⟨ cong (λ - → 𝕄S→𝕄S∘∥-∥₂ (n , -) .snd) (requot-comp v) ⟩
      𝕄S→𝕄S∘∥-∥₂ (n , [ v ]₂) .snd         ≡⟨⟩
      [ (λ k → ∣ v k ∣₂) ]₂ ∎

  lemma : (𝕄S→𝕄S∘∥-∥₂ (𝕄S∘∥-∥₂→𝕄S (n , v))) .snd ≡ v
  lemma = SQ.elimProp {P = λ v → 𝕄S→𝕄S∘∥-∥₂ (𝕄S∘∥-∥₂→𝕄S (n , v)) .snd ≡ v}
    (λ _ → SQ.squash/ _ _) step v

𝕄S∘∥-∥₂-𝕄S-Iso : Iso (𝕄S ∥ X ∥₂) (𝕄S X)
𝕄S∘∥-∥₂-𝕄S-Iso .fun = 𝕄S∘∥-∥₂→𝕄S
𝕄S∘∥-∥₂-𝕄S-Iso .inv = 𝕄S→𝕄S∘∥-∥₂
𝕄S∘∥-∥₂-𝕄S-Iso .rightInv = 𝕄S→𝕄S∘∥-∥₂→𝕄S
𝕄S∘∥-∥₂-𝕄S-Iso .leftInv = 𝕄S∘∥-∥₂→𝕄S→𝕄S∘∥-∥₂

𝕄S∘∥-∥₂≃𝕄S : 𝕄S ∥ X ∥₂ ≃ 𝕄S X
𝕄S∘∥-∥₂≃𝕄S = isoToEquiv 𝕄S∘∥-∥₂-𝕄S-Iso

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

module FMSet-OverBij where
  open import Cubical.Foundations.Isomorphism
    using
      ( invIso
      ; _Iso⟨_⟩_
      ; _∎Iso
      )
  open import Cubical.Foundations.Structure
  open import Cubical.Foundations.Transport
    using (pathToIso)

  open import Multiset.Bij
  open import Multiset.OverBij.Base as OverBij
    using
      ( Bag
      ; Vect
      ; BagIsoΣ
      ; Idx≡⟨Bij→FinSet⟩
      )
  open import Multiset.OverBij.Properties as OverBij
    using
      ( ωTree
      ; bagLimitIso
      )

  FMSetPreservesSetTruncTree : Iso (𝕄S ∥ ωTree ∥₂) ∥ ωTree ∥₂
  FMSetPreservesSetTruncTree =
    (𝕄S ∥ ωTree ∥₂)   Iso⟨ 𝕄S∘∥-∥₂-𝕄S-Iso ⟩
    (𝕄S ωTree)        Iso⟨ 𝕄S-∥𝕄G∥₂-Iso ⟩
    (∥ 𝕄G ωTree ∥₂)   Iso⟨ ST.setTruncIso (invIso step) ⟩
    (∥ ωTree ∥₂)      ∎Iso where

    BijFinSetIso : Iso Bij (FinSet ℓ-zero)
    BijFinSetIso = equivToIso Bij≃FinSet

    abstract
    Vect-⟨Bij→FinSet⟩-Iso : (x : Bij) → Iso (Vect ωTree x) (⟨ Bij→FinSet x ⟩ → ωTree)
    Vect-⟨Bij→FinSet⟩-Iso x = pathToIso (cong (λ X → X → ωTree) (Idx≡⟨Bij→FinSet⟩ x))

    step =
      (ωTree)               Iso⟨ bagLimitIso ⟩
      (Bag ωTree)           Iso⟨ BagIsoΣ ⟩
      (Σ Bij (Vect ωTree))  Iso⟨ Σ.Σ-cong-iso BijFinSetIso Vect-⟨Bij→FinSet⟩-Iso ⟩
      (𝕄G ωTree)            ∎Iso
