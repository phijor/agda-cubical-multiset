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

open import Multiset.Util using (Π⊥≡elim)

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
  private
    variable
      ℓA ℓB : Level
      A : Type ℓA
      B : Type ℓB

  elimₙ : ∀ {n} {P : (Fin n → ∥ X ∥₂) → Type ℓ'}
    → (setP : ∀ ∣v∣ → isSet (P ∣v∣))
    → (choice : (v : Fin n → X) → P (λ k → ∣ v k ∣₂))
    → (v : Fin n → ∥ X ∥₂) → P v
  elimₙ {n = ℕ.zero} {P = P} _ choice v =
    subst P (funExt ⊥.elim) (choice ⊥.elim)
  elimₙ {X = X} {n = suc n} {P = P} setP choice v = subst P {!   !} (choice {!   !}) where
    v₀ : ⊤ → ∥ X ∥₂
    v₀ = v ∘ inl

    v₋ : (k : Fin n) → ∥ X ∥₂
    v₋ = v ∘ fsuc

    induction : {! P (λ k → )  !}
    induction = {!   !} -- elimₙ {n = n} {!   !} {!   !} v₋


  setTrunc≃ : A ≃ B → ∥ A ∥₂ ≃ ∥ B ∥₂
  setTrunc≃ e = isoToEquiv (ST.setTruncIso (equivToIso e))

  ∥∥₂×∥∥₂→∥×∥₂ : ∥ A ∥₂ × ∥ B ∥₂ → ∥ A × B ∥₂
  ∥∥₂×∥∥₂→∥×∥₂ (∣a∣ , ∣b∣)= ST.rec2 ST.isSetSetTrunc (λ a b → ∣ a , b ∣₂) ∣a∣ ∣b∣

  ∥×∥₂→∥∥₂×∥∥₂ : ∥ A × B ∥₂ → ∥ A ∥₂ × ∥ B ∥₂
  ∥×∥₂→∥∥₂×∥∥₂ = ST.rec (isSet× isSetSetTrunc isSetSetTrunc) (λ (a , b) → ∣ a ∣₂ , ∣ b ∣₂)

  ∥∥₂-×-≃ : ∥ A ∥₂ × ∥ B ∥₂ ≃ ∥ A × B ∥₂
  ∥∥₂-×-≃ {A = A} {B = B} = isoToEquiv ∥∥₂-×-Iso where
    ∥∥₂-×-Iso : Iso (∥ A ∥₂ × ∥ B ∥₂) ∥ A × B ∥₂
    ∥∥₂-×-Iso .fun = ∥∥₂×∥∥₂→∥×∥₂
    ∥∥₂-×-Iso .inv = ∥×∥₂→∥∥₂×∥∥₂
    ∥∥₂-×-Iso .rightInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) λ _ → refl
    ∥∥₂-×-Iso .leftInv (∣a∣ , ∣b∣) = ST.elim2
      {C = λ a b → ∥∥₂-×-Iso .inv (∥∥₂-×-Iso .fun (a , b)) ≡ (a , b)}
      (λ x y → isProp→isSet (isSet× isSetSetTrunc isSetSetTrunc _ _))
      (λ a b → refl)
      ∣a∣ ∣b∣

    -- ∥ A ∥₂ × ∥ B ∥₂
    --   ≃⟨ invEquiv (ST.STIdempotent≃ (isSet× ST.isSetSetTrunc ST.isSetSetTrunc)) ⟩
    -- ∥ (∥ A ∥₂ × ∥ B ∥₂) ∥₂
    --   ≃⟨ {!   !} ⟩
    -- ∥ (A × ∥ B ∥₂) ∥₂
    --   ≃⟨ {!   !} ⟩
    -- ∥ A × B ∥₂
    --   ■

  module _ {ℓ : Level} {Y : (t : ⊤) → Type ℓ} where
    -- Helper: Function from the unit type into a set truncations form a set.
    isSetΠ⊤∥∥₂ : isSet ((t : ⊤) → ∥ Y t ∥₂)
    isSetΠ⊤∥∥₂ = isSetΠ (λ _ → isSetSetTrunc)

    -- Boxing:
    Π⊤∥∥₂→∥Π⊤∥₂ : ((t : ⊤) → ∥ Y t ∥₂) → ∥ ((t : ⊤) → Y t) ∥₂
    Π⊤∥∥₂→∥Π⊤∥₂ v = ST.elim (λ _ → isSetSetTrunc) (λ y₀ → ∣ const y₀ ∣₂) (v tt)

    -- Unboxing:
    ∥Π⊤∥→Π⊤∥∥₂ : ∥ ((t : ⊤) → Y t) ∥₂ → ((t : ⊤) → ∥ Y t ∥₂)
    ∥Π⊤∥→Π⊤∥∥₂ = ST.elim (λ _ → isSetΠ⊤∥∥₂) (∣_∣₂ ∘_)

    ∥∥₂-Π⊤-Iso : Iso ((t : ⊤) → ∥ Y t ∥₂) ∥ ((t : ⊤) → Y t) ∥₂
    ∥∥₂-Π⊤-Iso .fun = Π⊤∥∥₂→∥Π⊤∥₂
    ∥∥₂-Π⊤-Iso .inv = ∥Π⊤∥→Π⊤∥∥₂
    ∥∥₂-Π⊤-Iso .rightInv = ST.elim (λ ∣v∣ → isProp→isSet (isSetSetTrunc _ ∣v∣)) (λ v → refl)
    ∥∥₂-Π⊤-Iso .leftInv v = ST.elim
      {B = Motive}
      (λ ∣y∣ → isProp→isSet (isSetΠ⊤∥∥₂ _ (const ∣y∣)))
      (λ y₀ → refl)
      (v tt) where
        Motive : ∥ Y tt ∥₂ → Type ℓ
        Motive ∣y∣ = ∥Π⊤∥→Π⊤∥∥₂ (Π⊤∥∥₂→∥Π⊤∥₂ (const ∣y∣)) ≡ const ∣y∣

  setChoice≅Fin : {n : ℕ}
    → (Y : Fin n → Type ℓ')
    → Iso ((k : Fin n) → ∥ Y k ∥₂) ∥ ((k : Fin n) → Y k) ∥₂
  setChoice≅Fin {n = ℕ.zero} Y = iso₀ where

    iso₀ : Iso ((k : ⊥) → ∥ Y k ∥₂) ∥ ((k : ⊥) → Y k) ∥₂
    iso₀ .fun _ = ∣ ⊥.elim ∣₂
    iso₀ .inv _ = ⊥.elim
    iso₀ .rightInv = ST.elim (λ _ → isProp→isSet (isSetSetTrunc _ _)) (cong ∣_∣₂ ∘ Π⊥≡elim)
    iso₀ .leftInv  = Π⊥≡elim
  setChoice≅Fin {n = suc n} Y = isoₙ₊₁ where
    isoₙ₊₁ : Iso ((k : ⊤ ⊎ Fin n) → ∥ Y k ∥₂) ∥ ((k : ⊤ ⊎ Fin n) → Y k) ∥₂
    isoₙ₊₁ .fun v = ∣v∣ where
      vᵣ : (k : Fin n) → ∥ Y (fsuc k) ∥₂
      vᵣ = v ∘ inr

      ∣vᵣ∣ : ∥ ((k : Fin n) → Y (fsuc k)) ∥₂
      ∣vᵣ∣ = setChoice≅Fin (λ k → Y (fsuc k)) .fun vᵣ

      vₗ : (t : ⊤) → ∥ Y (inl t) ∥₂
      vₗ = v ∘ inl

      ∣vₗ∣ : ∥ ((t : ⊤) → Y (inl t)) ∥₂
      ∣vₗ∣ = Π⊤∥∥₂→∥Π⊤∥₂ vₗ

      ∣vₗ×vᵣ∣ : ∥ ((t : ⊤) → Y (inl t)) × ((k : Fin n) → Y (inr k)) ∥₂
      ∣vₗ×vᵣ∣ = ∥∥₂×∥∥₂→∥×∥₂ (∣vₗ∣ , ∣vᵣ∣)

      ∣v∣ : ∥ ((k : ⊤ ⊎ Fin n) → Y k) ∥₂
      ∣v∣ = ST.elim (λ _ → isSetSetTrunc) (λ (l , r) → ∣ Sum.elim l r ∣₂) ∣vₗ×vᵣ∣
    isoₙ₊₁ .inv = ST.rec (isSetΠ (λ _ → isSetSetTrunc)) λ v k → ∣ v k ∣₂
    isoₙ₊₁ .rightInv = goal where
      rec' : ∀ v → fun isoₙ₊₁ (inv isoₙ₊₁ ∣ v ∣₂) ≡ ∣ v ∣₂
      rec' = {!   !}

      goal : ∀ v → fun isoₙ₊₁ (inv isoₙ₊₁ v) ≡ v
      goal v = ST.elim {!   !} {!   !} v
    isoₙ₊₁ .leftInv  = {!   !}

  setChoice≃Fin : {n : ℕ}
    → (Y : Fin n → Type ℓ')
    → ((k : Fin n) → ∥ Y k ∥₂) ≃ ∥ ((k : Fin n) → Y k) ∥₂
  setChoice≃Fin {ℓ' = ℓ'} {n = 0} Y =
    ((k : ⊥) → ∥ Y k ∥₂)
      ≃⟨ ⊤.isContr→≃Unit ⊥.isContrΠ⊥ ⟩
    Unit
      ≃⟨ ⊤.Unit≃Unit* ⟩
    ⊤.Unit* {ℓ'}
      ≃⟨ invEquiv (ST.setTruncIdempotent≃ ⊤.isSetUnit*) ⟩
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
𝕄S∘∥-∥₂→𝕄S {X = X} (n , v) = SQ.elim (λ _ → OverSet.isSetFMSet) go well-defined v where
  open Choice

  box : ∥ (Fin n → X) ∥₂ → Fin n → ∥ X ∥₂
  box = Choice.setChoice≅Fin (λ _ → X) .inv

  unbox : (v : Fin n → ∥ X ∥₂) → ∥ (Fin n → X) ∥₂
  unbox = setChoice≅Fin (λ _ → X) .fun

  to-quot : ∥ (Fin n → X) ∥₂ → (Fin n → X) /₂ SymmetricAction n
  to-quot = ST.rec SQ.squash/ [_]₂

  go : (v : Fin n → ∥ X ∥₂) → 𝕄S X
  go v = n , to-quot (unbox v)

  -- well-defined' : ∀ v w → SymmetricAction n (box v) (box w) → to-quot v ≡ to-quot w
  -- well-defined' = ST.elim2 {!   !}
  --   (λ a b (σ , p) → SQ.eq/ _ _ (σ , {!   !}))

  well-defined : ∀ v w → SymmetricAction n v w → go v ≡ go w
  well-defined v→∣∣ w→∣∣ (σ , p) = ΣPathP (refl , goal) where
    v′ = unbox v→∣∣
    w′ = unbox w→∣∣

    goal : to-quot v′ ≡ to-quot w′
    goal = {!   !}
      -- ST.elim2
      -- {C = λ ∣v∣ ∣w∣ → ∣v∣ ≡ unbox v→∣∣ → ∣w∣ ≡ unbox w→∣∣ → to-quot ∣v∣ ≡ to-quot ∣w∣}
      -- (λ _ _ → {! SQ.is  !})
      -- (λ v w h₁ h₂ → SQ.eq/ v w (σ , ua→ (λ k → {! (ua→⁻ p k)  !}))) v′ w′ refl refl

𝕄S→𝕄S∘∥-∥₂ : 𝕄S X → 𝕄S ∥ X ∥₂
𝕄S→𝕄S∘∥-∥₂ (n , [v]) = n , SQ.rec SQ.squash/ go well-defined [v] where
  box : (Fin n → X) → (Fin n → ∥ X ∥₂)
  box v = ∣_∣₂ ∘ v

  go : (Fin n → X) → (Fin n → ∥ X ∥₂) /₂ SymmetricAction n
  go v = [ box v ]₂

  module _ (v w : Fin n → X) (v∼w : v ∼ w) where
    well-defined : go v ≡ go w
    well-defined = SQ.eq/ (box v) (box w) (OverSet.∼cong ∣_∣₂ v∼w)

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
