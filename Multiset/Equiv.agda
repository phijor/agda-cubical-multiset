module Multiset.Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
  using
    ( isoToEquiv
    ; iso
    )
open import Cubical.Foundations.HLevels
  using
    ( isSetΣ
    )
open import Cubical.Foundations.Function
  using
    ( _∘_
    ; 2-Constant
    )

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

open import Cubical.Data.Sigma as Σ
  using
    ( ΣPathP
    ; Σ≡Prop
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
SymmetricAction {X = X} n v w = Σ[ σ ∈ (Fin n ≃ Fin n) ] (λ i → (ua σ i → X)) [ v ≡ w ]

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
  is2Const α β = SetQuotients.eq/ {R = SymmetricAction n} _ _ (σ , (ua→ step₂)) where
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
