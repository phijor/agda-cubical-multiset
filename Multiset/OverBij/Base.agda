module Multiset.OverBij.Base where

open import Multiset.Bij as Bij

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Sigma as Σ
open import Cubical.Data.Nat as ℕ
  using (ℕ)

-- open import Cubical.Data.FinSet as FinSet

private
  variable
    ℓ : Level
    X Y : Type ℓ

abstract
  ⟨Bij→FinSet⟩ : Bij → Type ℓ-zero
  ⟨Bij→FinSet⟩ = λ x → ⟨ Bij→FinSet x ⟩

FMGpd : Type ℓ → Type ℓ
FMGpd X = Σ[ n ∈ Bij ] (⟨Bij→FinSet⟩ n → X)

FMGpdPathP : ∀ {m n : Bij}
  → (p : m ≡ n)
  → {v : ⟨Bij→FinSet⟩ m → X}
  → {w : ⟨Bij→FinSet⟩ n → X}
  → PathP (λ i → ⟨Bij→FinSet⟩ (p i) → X) v w
  → (m , v) ≡ (n , w)
FMGpdPathP perm q = λ i → (perm i) , (q i)

isGroupoidFMGpd : isGroupoid X → isGroupoid (FMGpd X)
isGroupoidFMGpd gpdX = isGroupoidΣ isGroupoidBij (λ x → isGroupoidΠ λ _ → gpdX)

map : (f : X → Y) → (FMGpd X → FMGpd Y)
map f (n , v) = n , f ∘ v

map∘map : ∀ {Z : Type ℓ} → (f : X → Y) (g : Y → Z)
  → (xs : FMGpd X)
  → map g (map f xs) ≡ map (g ∘ f) xs
map∘map f g (n , v) = refl
