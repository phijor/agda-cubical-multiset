module Multiset.Equiv where

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
  using
    ( isSetΣ
    ; isOfHLevel
    ; isOfHLevelΣ
    ; isOfHLevelΠ
    ; isSet×
    )
open import Cubical.Foundations.Function
  using
    ( _∘_
    ; 2-Constant
    )

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

open import Cubical.Data.Unit as ⊤
  using
    ( Unit
    )
open import Cubical.Data.Empty as ⊥
  using
    ( ⊥
    )
import Cubical.Data.Sum as Sum
open import Cubical.Data.Sigma as Σ
  using
    ( ΣPathP
    ; Σ≡Prop
    ; _×_
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    )
open import Cubical.Data.FinSet as FinSet
  using
    ( FinSet
    ; isFinSet
    ; isFinSetFin
    ; isPropIsFinSet
    )
open import Cubical.Data.SumFin as Fin

open import Cubical.HITs.SetQuotients as SetQuotients
  using
    ( _/_
    )
  renaming
    ( [_] to [_]₂
    )
open import Cubical.HITs.SetTruncation as SetTrunc
  using
    ( ∥_∥₂
    ; ∣_∣₂
    ; squash₂
    ; isSetSetTrunc
    )
open import Cubical.HITs.PropositionalTruncation as PropTrunc
  using
    ( ∥_∥
    ; ∣_∣
    )
open import Cubical.Relation.Binary as BinRel
  using
    ( Rel
    )

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

FinSet₀ : Type₁
FinSet₀ = FinSet ℓ-zero

𝕄G : Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
𝕄G X = Σ[ Y ∈ FinSet₀ ] (⟨ Y ⟩ → X)

𝕄GPathP : ∀ {V W : Type}
  → {finV : isFinSet V}
  → {finW : isFinSet W}
  → {v : V → X}
  → {w : W → X}
  → (p : V ≡ W)
  → (P : PathP (λ i → p i → X) v w)
  → Path (𝕄G X) ((V , finV) , v) (((W , finW) , w))
𝕄GPathP p P = ΣPathP ((Σ≡Prop (λ _ → isPropIsFinSet) p) , P)

isGroupoid𝕄G : isGroupoid X → isGroupoid (𝕄G X)
isGroupoid𝕄G h = isOfHLevelΣ 3 FinSet.isGroupoidFinSet λ _ → isOfHLevelΠ 3 (λ _ → h)

𝕄GPathP≃ : ∀ {V W : Type}
  → {finV : isFinSet V}
  → {finW : isFinSet W}
  → {v : V → X}
  → {w : W → X}
  → (α : V ≃ W)
  → (eq : ∀ k → v k ≡ w (equivFun α k))
  → Path (𝕄G X) ((V , finV) , v) (((W , finW) , w))
𝕄GPathP≃ α eq = 𝕄GPathP (ua α) (ua→ eq)

SymmetricAction : (n : ℕ) → Rel (Fin n → X) (Fin n → X) _
SymmetricAction {X = X} n v w = Σ[ σ ∈ (Fin n ≃ Fin n) ] PathP (λ i → (ua σ i → X)) v w

𝕄S : Type ℓ → Type ℓ
𝕄S X = Σ[ n ∈ ℕ ] (Fin n → X) / SymmetricAction n

𝕄S≡ : ∀ {n}
  → (v w : Fin n → X)
  → (σ : Fin n ≃ Fin n)
  → (p : (λ i → (ua σ i → X)) [ v ≡ w ])
  → Path (𝕄S X) (n , [ v ]₂) (n , [ w ]₂)
𝕄S≡ v w σ p = ΣPathP (refl , (SetQuotients.eq/ v w (σ , p)))

isSet𝕄 : isSet (𝕄S X)
isSet𝕄 = isSetΣ ℕ.isSetℕ (λ _ → SetQuotients.squash/)

𝕄S→∥𝕄G∥₂ : 𝕄S X → ∥ 𝕄G X ∥₂
𝕄S→∥𝕄G∥₂ (n , x) = SetQuotients.rec squash₂ f well-defined x where
  f : (Fin n → X) → ∥ 𝕄G X ∥₂
  f v = ∣ (Fin n , isFinSetFin) , v ∣₂

  well-defined : (v w : Fin n → X) → SymmetricAction n v w → f v ≡ f w
  well-defined v w (σ , v∘σ≡w) = cong ∣_∣₂ (𝕄GPathP (ua σ) v∘σ≡w)

𝕄G→𝕄S : 𝕄G X → 𝕄S X
𝕄G→𝕄S {X = X} ((Y , n , e) , v) = n , (PropTrunc.rec→Set SetQuotients.squash/ from-equiv is2Const e) where
  from-equiv : Y ≃ Fin n → (Fin n → X) / SymmetricAction n
  from-equiv α = [ v ∘ invEq α ]₂

  is2Const : (α β : Y ≃ Fin n) → [ v ∘ (invEq α) ]₂ ≡ [ v ∘ (invEq β) ]₂
  is2Const α β = SetQuotients.eq/ {R = SymmetricAction n} _ _ (σ , ua→ step₂) where
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
∥𝕄G∥₂→𝕄S = SetTrunc.rec isSet𝕄 𝕄G→𝕄S

-- Section
∥𝕄G∥₂→𝕄S→∥𝕄G∥₂ : (x : ∥ 𝕄G X ∥₂) → 𝕄S→∥𝕄G∥₂ (∥𝕄G∥₂→𝕄S x) ≡ x
∥𝕄G∥₂→𝕄S→∥𝕄G∥₂ {X = X} = SetTrunc.elim (λ _ → isProp→isSet (SetTrunc.squash₂ _ _)) go where

  module _ (Y : Type) (n : ℕ) (v : Y → X) (α : Y ≃ Fin n) where
    equiv-path :
      (λ i → ∥ ua (invEquiv α) i ≃ Fin n ∥) [ ∣ idEquiv (Fin n) ∣ ≡ ∣ α ∣ ]
    equiv-path = isProp→PathP (λ i → PropTrunc.isPropPropTrunc) _ _

    is-permutation : ∀ k → (v ∘ invEq α) k ≡ v (invEq α k)
    is-permutation _ = refl

    sect : ∣ (Fin n , n , ∣ idEquiv (Fin n) ∣) , v ∘ invEq α ∣₂ ≡ ∣ (Y , n , ∣ α ∣) , v ∣₂
    sect = cong ∣_∣₂ (𝕄GPathP≃ (invEquiv α) is-permutation)

  f : ∥ 𝕄G X ∥₂ → ∥ 𝕄G X ∥₂
  f x = 𝕄S→∥𝕄G∥₂ (∥𝕄G∥₂→𝕄S x)

  -- Proof by induction on the propositionally truncated
  -- equivalence (e : ∥ Y ≃ Fin k ∥):
  go : (x : 𝕄G X) → f ∣ x ∣₂ ≡ ∣ x ∣₂
  go ((Y , n , e) , v) = PropTrunc.elim
    -- Equality in a set truncation is a proposition:
    (λ α → let x = ∣ (Y , n , α) , v ∣₂ in squash₂ (f x) x)
    (sect Y n v)
    e

𝕄S→∥𝕄G∥₂→𝕄S : (x : 𝕄S X) → ∥𝕄G∥₂→𝕄S (𝕄S→∥𝕄G∥₂ x) ≡ x
𝕄S→∥𝕄G∥₂→𝕄S (n , v) = SetQuotients.elimProp
  {P = λ v → ∥𝕄G∥₂→𝕄S (𝕄S→∥𝕄G∥₂ (n , v)) ≡ (n , v)}
  (λ _ → isSet𝕄 _ _)
  (λ v → refl)
  v

𝕄S≃∥𝕄G∥₂ : 𝕄S X ≃ ∥ 𝕄G X ∥₂
𝕄S≃∥𝕄G∥₂ = isoToEquiv (iso 𝕄S→∥𝕄G∥₂ ∥𝕄G∥₂→𝕄S ∥𝕄G∥₂→𝕄S→∥𝕄G∥₂ 𝕄S→∥𝕄G∥₂→𝕄S)

module Choice where
  private
    variable
      ℓA ℓB : Level
      A : Type ℓA
      B : Type ℓB

  setTrunc≃ : A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
  setTrunc≃ e = isoToEquiv (SetTrunc.setTruncIso (equivToIso e))

  ∥∥₂-×-≃ : ∥ A ∥₂ × ∥ B ∥₂ ≃ ∥ A × B ∥₂
  ∥∥₂-×-≃ {A = A} {B = B} = isoToEquiv ∥∥₂-×-Iso where
    open Iso
    ∥∥₂-×-Iso : Iso (∥ A ∥₂ × ∥ B ∥₂) ∥ A × B ∥₂
    ∥∥₂-×-Iso .fun (∣a∣ , ∣b∣) = SetTrunc.rec2 isSetSetTrunc f ∣a∣ ∣b∣ where
      f : A → B → ∥ A × B ∥₂
      f a b = ∣ a , b ∣₂
    ∥∥₂-×-Iso .inv = SetTrunc.rec (isSet× isSetSetTrunc isSetSetTrunc) λ (a , b) → ∣ a ∣₂ , ∣ b ∣₂
    ∥∥₂-×-Iso .rightInv = SetTrunc.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) λ _ → refl
    ∥∥₂-×-Iso .leftInv (∣a∣ , ∣b∣) = SetTrunc.elim2
      {C = λ a b → ∥∥₂-×-Iso .inv (∥∥₂-×-Iso .fun (a , b)) ≡ (a , b)}
      (λ x y → isProp→isSet (isSet× isSetSetTrunc isSetSetTrunc _ _))
      (λ a b → refl)
      ∣a∣ ∣b∣

    -- ∥ A ∥₂ × ∥ B ∥₂
    --   ≃⟨ invEquiv (SetTrunc.setTruncIdempotent≃ (isSet× SetTrunc.isSetSetTrunc SetTrunc.isSetSetTrunc)) ⟩
    -- ∥ (∥ A ∥₂ × ∥ B ∥₂) ∥₂
    --   ≃⟨ {!   !} ⟩
    -- ∥ (A × ∥ B ∥₂) ∥₂
    --   ≃⟨ {!   !} ⟩
    -- ∥ A × B ∥₂
    --   ■

  setChoice≃Fin : {n : ℕ}
    → (Y : Fin n → Type ℓ')
    → ((k : Fin n) → ∥ Y k ∥₂) ≃ ∥ ((k : Fin n) → Y k) ∥₂
  setChoice≃Fin {ℓ' = ℓ'} {n = 0} Y =
    ((k : ⊥) → ∥ Y k ∥₂)
      ≃⟨ ⊤.isContr→≃Unit ⊥.isContrΠ⊥ ⟩
    Unit
      ≃⟨ ⊤.Unit≃Unit* ⟩
    ⊤.Unit* {ℓ'}
      ≃⟨ invEquiv (SetTrunc.setTruncIdempotent≃ ⊤.isSetUnit*) ⟩
    ∥ ⊤.Unit* {ℓ'} ∥₂
      ≃⟨ setTrunc≃ (invEquiv ⊤.Unit≃Unit*) ⟩
    ∥ ⊤.Unit ∥₂
      ≃⟨ setTrunc≃ (invEquiv (⊤.isContr→≃Unit ⊥.isContrΠ⊥)) ⟩
    ∥ ((k : ⊥) → Y k) ∥₂
      ■
  setChoice≃Fin {n = suc n} Y =
    ((k : ⊤ ⊎ Fin n) → ∥ Y k ∥₂)
      ≃⟨ Sum.Π⊎≃ ⟩
    ((_ : ⊤) → ∥ Y (inl _) ∥₂) × ((k : Fin n) → ∥ Y (fsuc k) ∥₂)
      ≃⟨ Σ.Σ-cong-equiv-fst (⊤.ΠUnit (λ x → ∥ Y (inl x) ∥₂)) ⟩
    ∥ Y (inl ⊤.tt) ∥₂ × ((k : Fin n) → ∥ Y (fsuc k) ∥₂)
      ≃⟨ Σ.Σ-cong-equiv-snd (λ _ → setChoice≃Fin {n = n} λ k → Y (inr k)) ⟩
    ∥ Y (inl ⊤.tt) ∥₂ × ∥ ((k : Fin n) → Y (fsuc k) )∥₂
      ≃⟨ Σ.Σ-cong-equiv-fst (setTrunc≃ (invEquiv (⊤.ΠUnit (λ x → Y (inl x))))) ⟩
    ∥ ((_ : ⊤) → Y (inl _)) ∥₂ × ∥ ((k : Fin n) → Y (fsuc k) )∥₂
      ≃⟨ ∥∥₂-×-≃ ⟩
    ∥ ((_ : ⊤) → Y (inl _)) × ((k : Fin n) → Y (inr k)) ∥₂
      ≃⟨ setTrunc≃ (invEquiv Sum.Π⊎≃) ⟩
    ∥ ((k : ⊤ ⊎ Fin n) → Y k) ∥₂
      ■

-- Idempotency of 𝕄S on set truncations:

𝕄S∘∥-∥₂→𝕄S : 𝕄S ∥ X ∥₂ → 𝕄S X
𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = SetQuotients.elim (λ _ → isSet𝕄) go well-defined v where

  box : ∥ (Fin n → X) ∥₂ → Fin n → ∥ X ∥₂
  box = invEq (Choice.setChoice≃Fin (λ _ → X))

  unbox : (v : Fin n → ∥ X ∥₂) → ∥ (Fin n → X) ∥₂
  unbox = equivFun (Choice.setChoice≃Fin (λ _ → X))

  to-quot : ∥ (Fin n → X) ∥₂ → (Fin n → X) / SymmetricAction n
  to-quot = SetTrunc.rec SetQuotients.squash/ [_]₂

  go : (v : Fin n → ∥ X ∥₂) → 𝕄S X
  go v = n , to-quot (unbox v)

  well-defined' : ∀ v w → SymmetricAction n (box v) (box w) → to-quot v ≡ to-quot w
  well-defined' = SetTrunc.elim2 {!   !} (λ a b (σ , p) → SetQuotients.eq/ _ _ (σ , {! box ∣ a ∣₂  !}))

  well-defined : ∀ v w → SymmetricAction n v w → go v ≡ go w
  well-defined v w (σ , p) = ΣPathP (refl , goal) where
    v′ = unbox v
    w′ = unbox w

    goal : SetTrunc.rec SetQuotients.squash/ [_]₂ v′
      ≡ SetTrunc.rec SetQuotients.squash/ [_]₂ w′
    goal = {!   !}

ua→cong : ∀ {ℓ ℓ' ℓ''} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁}
  {B : (i : I) → Type ℓ'}
  {C : (i : I) → Type ℓ''}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  (F : {i : I} → B i → C i)
  (p : PathP (λ i → ua e i → B i) f₀ f₁)
  → PathP (λ i → ua e i → C i) (F {i0} ∘ f₀) (F {i1} ∘ f₁)
ua→cong F p = λ i x → F (p i x)

ua→cong≡ua→∘cong∘ua→⁻ : ∀ {ℓ ℓ' ℓ''} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁}
  {B : (i : I) → Type ℓ'}
  {C : (i : I) → Type ℓ''}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  (F : {i : I} → B i → C i)
  (p : PathP (λ i → ua e i → B i) f₀ f₁)
  → ua→cong F p ≡ ua→ λ a i → F (ua→⁻ p a i)
ua→cong≡ua→∘cong∘ua→⁻ F p = {!  !}

𝕄S→𝕄S∘∥-∥₂ : 𝕄S X → 𝕄S ∥ X ∥₂
𝕄S→𝕄S∘∥-∥₂ (n , [v]) = n , SetQuotients.rec SetQuotients.squash/ go well-defined [v] where
  box : (Fin n → X) → (Fin n → ∥ X ∥₂)
  box v = ∣_∣₂ ∘ v

  go : (Fin n → X) → (Fin n → ∥ X ∥₂) / SymmetricAction n
  go v = [ box v ]₂

  module _ (v w : Fin n → X) ((σ , r) : SymmetricAction n v w) where
    rel-box : SymmetricAction n (box v) (box w)
    rel-box = σ , ua→cong ∣_∣₂ r

    well-defined : go v ≡ go w
    well-defined = SetQuotients.eq/ (box v) (box w) rel-box

𝕄S∘∥-∥₂≃𝕄S : 𝕄S ∥ X ∥₂ ≃ 𝕄S X
𝕄S∘∥-∥₂≃𝕄S = isoToEquiv (iso 𝕄S∘∥-∥₂→𝕄S 𝕄S→𝕄S∘∥-∥₂ {!   !} {!   !})
