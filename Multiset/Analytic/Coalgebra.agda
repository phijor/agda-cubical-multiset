module Multiset.Analytic.Coalgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Multiset.Analytic.Base
open import Multiset.Analytic.Functor

private
  variable
    ℓ ℓG ℓS ℓX ℓY ℓZ ℓσ : Level

module _ (Sig : Signature ℓG ℓS ℓσ) where

  open module F = Functor Sig

  Coalgebra : ∀ ℓ → Type (ℓ-max (ℓ-max (ℓ-max ℓG ℓS) ℓσ) (ℓ-suc ℓ))
  Coalgebra ℓ = TypeWithStr ℓ (λ C → (C → C F./∼))

  IsCoalgebraMap : (C D : Coalgebra ℓ) (f : ⟨ C ⟩ → ⟨ D ⟩) → Type (ℓ-max (ℓ-max (ℓ-max ℓG ℓS) ℓσ) ℓ)
  IsCoalgebraMap (C , γ) (D , δ) f = δ ∘ f ≡ (f /ₘ∼) ∘ γ

  record CoalgebraMap {ℓ : Level} (C D : Coalgebra ℓ) : Type (ℓ-max (ℓ-max (ℓ-max ℓG ℓS) ℓσ) ℓ) where
    field
      map : ⟨ C ⟩ → ⟨ D ⟩
      isCoalgebraMap : IsCoalgebraMap C D map

  _⇒_ : {ℓ : Level} (C D : Coalgebra ℓ) → Type _
  C ⇒ D = CoalgebraMap C D

  infixr 5 _⇒_
