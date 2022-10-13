{-# OPTIONS --safe #-}

module Multiset.Inductive.Order where

open import Multiset.Prelude
open import Multiset.Inductive.Base as M

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using (flip)
open import Cubical.Foundations.Structure

open import Cubical.Functions.Logic as Logic

open import Cubical.Data.Sigma as Simga

open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
    ; ∥_∥₁
    ; isPropPropTrunc
    )

module _ {ℓ : Level} {X : Type ℓ} where

  -- ⊕-cancel : ∀ xs {ys₁ ys₂ : M X}
  --   → xs ⊕ ys₁ ≡ xs ⊕ ys₂
  --   → ys₁ ≡ ys₂
  -- ⊕-cancel xs {ys₁} {ys₂} = M.ind {P = λ xs → ∀ ys₁ ys₂ → xs ⊕ ys₁ ≡ xs ⊕ ys₂ → ys₁ ≡ ys₂}
  --   (λ _ → isPropΠ3 λ _ _ _ → isSetM _ _)
  --   {! !} {! !} {! !} xs ys₁ ys₂
  
  _⊆′_ : M X → M X → Type ℓ
  xs ⊆′ ys = Σ[ vs ∈ M X ] xs ⊕ vs ≡ ys

  -- isProp-⊆′ : ∀ xs ys → isProp (xs ⊆′ ys)
  -- isProp-⊆′ xs ys = {! !}

  _⊆ₚ_ : M X → M X → hProp ℓ
  -- xs ⊆ₚ ys = ∃[ zs ∶ M X ] (((xs ⊕ zs) ≡ ys) , isSetM _ _)
  xs ⊆ₚ ys = ∃[ zs ∶ M X ] (xs ⊕ zs) ≡ₚ ys

  _⊆_ : M X → M X → Type ℓ
  xs ⊆ ys = ⟨ xs ⊆ₚ ys ⟩

  isProp-⊆ : ∀ {xs ys} → isProp (xs ⊆ ys)
  isProp-⊆ = str (_ ⊆ₚ _)

  _⊇ₚ_ : M X → M X → hProp ℓ
  _⊇ₚ_ = flip _⊆ₚ_

  _⊇_ : M X → M X → Type ℓ
  _⊇_ = flip _⊆_

  infix 80 _⊆_ _⊇_
  infix 80 _⊆ₚ_ _⊇ₚ_

  ⊆-refl : ∀ {xs : M X} → xs ⊆ xs
  ⊆-refl {xs = xs} = ∣ ε , ∣ unit' xs ∣₁ ∣₁

  ⊆-trans : ∀ {xs ys zs}
    → xs ⊆ ys
    → ys ⊆ zs
    → xs ⊆ zs
  ⊆-trans {xs = xs} {ys} {zs} = PT.rec2 isProp-⊆ goal where
    step : ∀ {us vs}
      → xs ⊕ us ≡ ys
      → ys ⊕ vs ≡ zs
      → xs ⊆ zs
    step {us} {vs} p q = ∣ us ⊕ vs , ∣ r ∣₁ ∣₁ where
      r =
        xs ⊕ (us ⊕ vs) ≡⟨ assoc _ _ _ ⟩
        (xs ⊕ us) ⊕ vs ≡⟨ cong (_⊕ vs) p ⟩
        ys ⊕ vs        ≡⟨ q ⟩
        zs ∎

    goal :
        Σ[ us ∈ M X ] ∥ xs ⊕ us ≡ ys ∥₁
      → Σ[ vs ∈ M X ] ∥ ys ⊕ vs ≡ zs ∥₁
      → xs ⊆ zs
    goal (us , p-us) (vs , p-vs) = PT.rec2 isProp-⊆ step p-us p-vs

  -- ε-unit-unique : ∀ {xs : M X} es
  --   → xs ⊕ es ≡ xs
  --   → es ≡ ε
  -- ε-unit-unique {xs = xs} = M.ind {P = λ xs → ∀ es → xs ⊕ es ≡ xs → es ≡ ε}
  --   (λ _ → isPropΠ2 λ _ _ → isSetM _ ε) empty* {! !} {! !} xs where
  --   empty* : ∀ es → ε ⊕ es ≡ ε → es ≡ ε
  --   empty* es ε⊕es≡ε =
  --     es ≡⟨ sym (unit es) ⟩
  --     ε ⊕ es ≡⟨ ε⊕es≡ε ⟩
  --     ε ∎

  -- ⊆-antisymm : ∀ {xs ys}
  --   → xs ⊆ ys
  --   → ys ⊆ xs
  --   → xs ≡ ys
  -- ⊆-antisymm {xs} {ys} = PT.rec2 (isSetM _ _) goal where
  --   step : ∀ {us vs}
  --     → xs ⊕ us ≡ ys
  --     → ys ⊕ vs ≡ xs
  --     → xs ≡ ys
  --   step {us} {vs} p q = {! ε-unit-unique (us ⊕ vs) us⊕vs-unitl !} where
  --     us⊕vs-unitl : xs ⊕ (us ⊕ vs) ≡ xs
  --     us⊕vs-unitl =
  --       xs ⊕ (us ⊕ vs) ≡⟨ assoc _ _ _ ⟩
  --       (xs ⊕ us) ⊕ vs ≡⟨ cong (_⊕ vs) p ⟩
  --       ys ⊕ vs ≡⟨ q ⟩
  --       xs ∎

  --   goal :
  --       Σ[ us ∈ M X ] ∥ xs ⊕ us ≡ ys ∥₁
  --     → Σ[ vs ∈ M X ] ∥ ys ⊕ vs ≡ xs ∥₁
  --     → xs ≡ ys
  --   goal (us , p-us) (vs , p-vs) = PT.rec2 (isSetM _ _) step p-us p-vs

  -- ⊆-η-inj : ∀ {x y : X}
  --   → (setX : isSet X)
  --   → η x ⊆ η y
  --   → x ≡ y
  -- ⊆-η-inj setX = PT.rec (setX _ _) λ (zs , p) → {! !}
