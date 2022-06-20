module Multiset.Bij.Base where

open import Multiset.Util.Path
  using (compPathOver ; compPathOver≡comp)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws
  using
    ( assoc
    ; lCancel
    ; rUnit
    ; lUnit
    ; _⁻¹
    )

open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    )
open import Cubical.Data.SumFin as Fin
  using
    ( Fin
    )

data Bij : Type where
  obj : (n : ℕ) → Bij
  hom : {m n : ℕ} → (α : Fin m ≃ Fin n) → obj m ≡ obj n
  id-coh : (n : ℕ) → hom {n = n} (idEquiv _) ≡ refl
  comp-coh : {m n o : ℕ}
    → (α : Fin m ≃ Fin n)
    → (β : Fin n ≃ Fin o)
    → hom (α ∙ₑ β) ≡ hom α ∙ hom β
  trunc : isGroupoid Bij

isGroupoidBij : isGroupoid Bij
isGroupoidBij = trunc

isSetBijPath : {x y : Bij} → isSet (x ≡ y)
isSetBijPath = isGroupoidBij _ _

private
  infix 40 _⁻ᵉ

  _⁻ᵉ : ∀ {m n} → Fin m ≃ Fin n → Fin n ≃ Fin m
  α ⁻ᵉ = invEquiv α

-- `hom` is functor of groupoids, so in particular it preserves inverses.
-- We first show that inverse equivalences compose to `refl` under `hom`
-- (hom-inv-comp), and deduce from that the coherence law for inverses
-- (inv-coh).
hom-inv-comp : ∀ {m n} (α : Fin m ≃ Fin n) → hom (α ⁻ᵉ) ∙ hom α ≡ refl
hom-inv-comp α =
  hom (α ⁻ᵉ) ∙ hom α    ≡⟨ sym (comp-coh _ _) ⟩
  hom (α ⁻ᵉ ∙ₑ α)       ≡⟨ cong hom (invEquiv-is-linv α) ⟩
  hom (idEquiv (Fin _)) ≡⟨ id-coh _ ⟩
  refl ∎

inv-coh : ∀ {m n} (α : Fin m ≃ Fin n) → hom (α ⁻ᵉ) ≡ (hom α) ⁻¹
inv-coh α =
  hom (α ⁻ᵉ)                        ≡⟨ rUnit (hom (α ⁻ᵉ)) ⟩
  hom (α ⁻ᵉ) ∙ refl                 ≡⟨ cong (hom (α ⁻ᵉ) ∙_) (sym (lCancel _)) ⟩
  hom (α ⁻ᵉ) ∙ (hom α ∙ (hom α) ⁻¹) ≡⟨ assoc _ (hom α) ((hom α) ⁻¹) ⟩
  (hom (α ⁻ᵉ) ∙ hom α) ∙ (hom α) ⁻¹ ≡⟨ cong (_∙ (hom α) ⁻¹) (hom-inv-comp α) ⟩
  refl ∙ (hom α) ⁻¹                 ≡⟨ sym (lUnit _) ⟩
  (hom α) ⁻¹ ∎

elim : ∀ {ℓ} {B : Bij → Type ℓ}
  → (gpdB : (x : Bij) → isGroupoid (B x))
  → (obj* : (n : ℕ) → B (obj n))
  → (hom* : ∀ {m n} → (α : Fin m ≃ Fin n) → PathP (λ j → B (hom α j)) (obj* m) (obj* n))
  → (id-coh* : (n : ℕ)
      → SquareP (λ i j → B (id-coh n i j))
        (hom* (idEquiv (Fin n))) -- top
        (refl {x = obj* n})      -- bottom
        (refl {x = obj* n})      -- left
        (refl {x = obj* n})      -- right
    )
  → (comp-coh* : ∀ {m n o} → (α : Fin m ≃ Fin n) → (β : Fin n ≃ Fin o)
      → SquareP (λ i j → (B (comp-coh α β i j)))
        (hom* (α ∙ₑ β))
        (compPathP' {B = B} (hom* α) (hom* β))
        (refl {x = obj* m})
        (refl {x = obj* o})
    )
  → (x : Bij) → B x
elim {B = B} gpdB obj* hom* id-coh* comp-coh* = go where
  go : (x : Bij) → B x
  go (obj n) = obj* n
  go (hom α i) = hom* α i
  go (id-coh n i j) = id-coh* n i j
  go (comp-coh α β i j) = comp-coh* α β i j
  go (trunc x y p q p≡q₁ p≡q₂ i j k) =
    gpdBDep _ _ _ _
      (λ j k → go (p≡q₁ j k)) (λ j k → go (p≡q₂ j k))
      (trunc x y p q p≡q₁ p≡q₂)
      i j k
    where
      gpdBDep : isOfHLevelDep 3 B
      gpdBDep = isOfHLevel→isOfHLevelDep 3 gpdB

elimSet : ∀ {ℓ} {B : Bij → Type ℓ}
  → (setB : (x : Bij) → isSet (B x))
  → (obj* : (n : ℕ) → B (obj n))
  → (hom* : ∀ {m n} → (α : Fin m ≃ Fin n) → PathP (λ j → B (hom α j)) (obj* m) (obj* n))
  → (x : Bij) → B x
elimSet {B = B} setB obj* hom* = elim (isSet→isGroupoid ∘ setB) obj* hom* id-coh* comp-coh* where
  id-coh* : ∀ n →
    SquareP (λ i j → B (id-coh n i j))
      (hom* (idEquiv (Fin n)))
      (refl {x = obj* n})
      (refl {x = obj* n})
      (refl {x = obj* n})
  id-coh* n = isSet→SquareP (λ i j → setB _) _ _ _ _

  comp-coh* : ∀ {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o)
    → SquareP (λ i j → B (comp-coh α β i j))
      (hom* (α ∙ₑ β))
      (compPathP' {B = B} (hom* α) (hom* β))
      (refl {x = obj* m})
      (refl {x = obj* o})
  comp-coh* α β = isSet→SquareP (λ i j → setB _) _ _ _ _

elimProp : ∀ {ℓ} {P : Bij → Type ℓ}
  → (propP : (x : Bij) → isProp (P x))
  → (obj* : (n : ℕ) → P (obj n))
  → (x : Bij) → P x
elimProp {P = P} propP obj* = elimSet (isProp→isSet ∘ propP) obj* hom* where
  hom* : ∀ {m n : ℕ} (α : Fin m ≃ Fin n)
    → PathP (λ j → P (hom α j)) (obj* m) (obj* n)
  hom* α = isProp→PathP (λ i → propP (hom α i)) (obj* _) (obj* _)

elimProp2 : ∀ {ℓ} {P : Bij → Bij → Type ℓ}
  → (propP : ∀ x y → isProp (P x y))
  → (obj* : (m n : ℕ) → P (obj m) (obj n))
  → (x y : Bij) → P x y
elimProp2 {P = P} propP obj* = elimProp
  (λ x → isPropΠ (λ y → propP x y))
  ( λ m
    → elimProp (λ y → propP (obj m) y) (obj* m)
  )

rec : ∀ {ℓ} {A : Type ℓ}
  → (gpdA : isGroupoid A)
  → (obj* : ℕ → A)
  → (hom* : ∀ {m n} → Fin m ≃ Fin n → obj* m ≡ obj* n)
  → (id-coh* : ∀ n → hom* {n = n} (idEquiv _) ≡ refl)
  → (comp-coh* : ∀ {m n o}
      → (α : Fin m ≃ Fin n)
      → (β : Fin n ≃ Fin o)
      → hom* (α ∙ₑ β) ≡ hom* α ∙ hom* β
    )
  → Bij → A
rec {A = A} gpdA obj* hom* id-coh* comp-coh* = elim {B = λ _ → A} (λ _ → gpdA) obj* hom* id-coh* comp-coh*′ where
  module _ {m n o : ℕ} (α : Fin m ≃ Fin n) (β : Fin n ≃ Fin o) where
    -- `elim` expects a dependent path composition (compPathP') in its
    -- `comp-coh*` argument, but we're given an ordinary, non-dependent
    -- path composition.
    -- Path composition and dependent path composition over a constant
    -- family (here `A`) are are propositionally equal, so we use that
    -- to adjust `comp-coh*`.
    adjust : (hom* α ∙ hom* β) ≡ compPathOver (hom α) (hom β) (hom* α) (hom* β)
    adjust = sym (compPathOver≡comp (hom α) (hom β) (hom* α) (hom* β))

    comp-coh*′ : hom* (α ∙ₑ β) ≡ compPathOver (hom α) (hom β) (hom* α) (hom* β)
    comp-coh*′ = comp-coh* α β ∙ adjust
