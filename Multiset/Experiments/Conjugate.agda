module Multiset.Experiments.Conjugate where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Equiv
  renaming
    ( invEquiv to infix 40 _⁻¹
    )

open import Cubical.HITs.PropositionalTruncation as PT

conjugate′ : ∀ {ℓ} {A K : Type ℓ} → A ≃ K → A ≃ A → K ≃ K
conjugate′ ε α = (ε ⁻¹) ∙ₑ α ∙ₑ ε

-- Conjugation is not a 2-constant operation. Duh.
module CounterExample where
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Data.SumFin
  open import Cubical.Data.Empty
  open import Cubical.Algebra.SymmetricGroup
  open import Cubical.Relation.Nullary.Base


  conj : Fin 3 ≃ Fin 3 → Fin 3 ≃ Fin 3 → Fin 3 ≃ Fin 3
  conj = conjugate′

  -- ⎛ 0 1 2 ⎞
  -- ⎝ 0 2 1 ⎠
  α-fun : Fin 3 → Fin 3
  α-fun fzero = fzero
  α-fun (fsuc fzero) = fsuc (fsuc fzero)
  α-fun (fsuc (fsuc fzero)) = fsuc fzero

  α : Fin 3 ≃ Fin 3
  α = isoToEquiv (iso α-fun α-fun α-inv α-inv) where
    α-inv : ∀ k → α-fun (α-fun k) ≡ k
    α-inv (inl x) = refl
    α-inv (fsuc (inl x)) = refl
    α-inv (fsuc (fsuc (inl x))) = refl

  -- ⎛ 0 1 2 ⎞
  -- ⎝ 1 0 2 ⎠
  η-fun : Fin 3 → Fin 3
  η-fun fzero = fsuc fzero
  η-fun (fsuc fzero) = fzero
  η-fun (fsuc (fsuc fzero)) = (fsuc (fsuc fzero))

  η : Fin 3 ≃ Fin 3
  η = isoToEquiv (iso η-fun η-fun η-inv η-inv) where
    η-inv : ∀ k → η-fun (η-fun k) ≡ k
    η-inv fzero = refl
    η-inv (fsuc fzero) = refl
    η-inv (fsuc (fsuc fzero)) = refl

  counterExample : ¬ (conj α (idEquiv _) ≡ conj α η)
  counterExample ch = not-that that where
    that : fzero ≡ fsuc (fsuc fzero)
    that = funExt⁻ (cong fst ch) ((fzero))

    not-that : ¬ (fzero ≡ fsuc (fsuc fzero))
    not-that = SumFin≡≃ 3 fzero (fsuc (fsuc fzero)) .fst
