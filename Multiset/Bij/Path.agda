module Multiset.Bij.Path where

open import Multiset.Bij.Base as Bij

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

open import Cubical.Data.Sigma as Sigma
  using (Σ≡Prop ; ΣPathP)
open import Cubical.Data.Nat as ℕ
  using (ℕ)
open import Cubical.Data.SumFin as Fin
  using (Fin)

hSet₀ : Type₁
hSet₀ = hSet ℓ-zero

isSetFin≃ : (m n : ℕ) → isSet (Fin m ≃ Fin n)
isSetFin≃ m n = isOfHLevel≃ 2 (Fin.isSetFin) (Fin.isSetFin)

Fin≃ : (m n : ℕ) → hSet₀
Fin≃ m n = (Fin m ≃ Fin n) , isSetFin≃ m n

preComp' : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
  → (α : X ≃ Y)
  → (Z ≃ X) ≃ (Z ≃ Y)
preComp' {X = X} {Y = Y} {Z = Z} α = isoToEquiv (iso (λ (β : Z ≃ X) → β ∙ₑ α) (λ (β : Z ≃ Y) → β ∙ₑ (invEquiv α)) {!   !} {!   !})

preComp : ∀ {m n} (k : ℕ) (α : Fin m ≃ Fin n) → (Fin k ≃ Fin m) ≃ (Fin k ≃ Fin n)
preComp k α = equivComp (idEquiv (Fin k)) α

Fin≃Path : ∀ {m n : ℕ} (k : ℕ) → Fin m ≃ Fin n → Fin≃ k m ≡ Fin≃ k n
Fin≃Path {m = m} {n = n} k α = TypeOfHLevel≡ 2 path where
  path : (Fin k ≃ Fin m) ≡ (Fin k ≃ Fin n)
  path = ua (preComp' α)

_ : Type
_ = {!  cong ΣPathP !}

-- TODO: Define "ΣSquareP r s = cong ΣPathP (ΣPath (r , s))

Fin≃PathId : (m n : ℕ) → Fin≃Path m (idEquiv (Fin n)) ≡ refl {x = Fin≃ m n}
Fin≃PathId m n = cong ΣPathP (ΣPathP (cong ua lemma ∙ uaIdEquiv , isSet→SquareP (λ i j → isSetΠ2 (λ x y → isProp→isSet isPropIsProp)) _ _ _ _)) where
  lemma : (preComp' (idEquiv (Fin n))) ≡ idEquiv (Fin m ≃ Fin n)
  lemma = equivEq (funExt
    ( λ α →
      α ∙ₑ (idEquiv (Fin n))
        ≡⟨ compEquivEquivId _ ⟩
      α
        ∎
    ))

Fin≃PathComp : ∀ {m n o : ℕ} (k : ℕ)
  → (α : Fin m ≃ Fin n)
  → (β : Fin n ≃ Fin o) →
      Fin≃Path k (α ∙ₑ β) ≡ Fin≃Path k α ∙ Fin≃Path k β
Fin≃PathComp k α β = cong ΣPathP (ΣPathP (cong ua lemma ∙ uaCompEquiv (preComp' α) (preComp' β) , isSet→SquareP (λ i j → isSetΠ2 (λ x y → isProp→isSet isPropIsProp)) _ _ _ _)) where
  lemma : (preComp' (α ∙ₑ β)) ≡ preComp' α ∙ₑ preComp' β
  lemma = equivEq (funExt (λ γ →
    γ ∙ₑ (α ∙ₑ β)
      ≡⟨ compEquiv-assoc _ _ _ ⟩
    (γ ∙ₑ α) ∙ₑ β
      ∎))

Code : ℕ → Bij → hSet₀
Code m = rec (isOfHLevelTypeOfHLevel 2)
  (λ n → Fin≃ m n)
  (Fin≃Path m)
  (Fin≃PathId m)
  (Fin≃PathComp m)
