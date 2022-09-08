module Multiset.Util.Logic where

open import Multiset.Prelude

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence

open import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma as Sigma
open import Cubical.Data.Unit as Unit
open import Cubical.Data.Sum as Sum

open import Cubical.Relation.Nullary.Base
  renaming (¬_ to infix 6 ¬_)

private
  variable
    ℓ : Level

_xor_ : Type ℓ → Type ℓ → Type ℓ
A xor B = (A × ¬ B) ⊎ (¬ A × B)

infixl 8 _xor_

module _ {A B : Type ℓ} where
  open import Cubical.Data.Sum as Sum
    using ()
    renaming
      ( inl to xorl
      ; inr to xorr
      ) public

  xorElim : ∀ {ℓ'} {C : A xor B → Type ℓ'}
    → ((pˡ : A × ¬ B) → C (xorl pˡ))
    → ((pʳ : ¬ A × B) → C (xorr pʳ))
    → (p : A xor B) → C p
  xorElim = Sum.elim

  isPropXor : isProp A → isProp B → isProp (A xor B)
  isPropXor propA propB = go where
    isPropA×¬B : isProp (A × (¬ B))
    isPropA×¬B = isProp× propA (isPropΠ λ _ → Empty.isProp⊥)

    isProp¬A×B : isProp ((¬ A) × B)
    isProp¬A×B = isProp× (isPropΠ λ _ → Empty.isProp⊥) propB

    go : (p q : A xor B) → p ≡ q
    go (inl p₁) (inl p₂) = cong Sum.inl (isPropA×¬B p₁ p₂)
    go (inl (a , _)) (inr (¬a , _)) = Empty.rec (¬a a)
    go (inr (¬a , _)) (inl (a , _)) = Empty.rec (¬a a)
    go (inr p₁) (inr p₂) = cong Sum.inr (isProp¬A×B p₁ p₂)

module _ {ℓ} (B : Type ℓ) where
  open Iso

  xor-identityˡ-Iso : Iso (⊥* xor B) B
  xor-identityˡ-Iso =
    (⊥* × ¬ B) ⊎ (¬ ⊥* × B) Iso⟨ Sum.⊎Iso iso₁ iso₂ ⟩
    ⊥ ⊎ B                   Iso⟨ Sum.⊎-swap-Iso {A = ⊥} {B = B} ⟩
    B ⊎ ⊥                   Iso⟨ Sum.⊎-⊥-Iso ⟩
    B                       ∎Iso where
    
    iso₁ : Iso (⊥* × ¬ B) ⊥
    iso₁ =
      ⊥* × ¬ B  Iso⟨ Sigma.Σ-cong-iso-fst (invIso LiftIso) ⟩
      ⊥  × ¬ B  Iso⟨ Sigma.ΣEmptyIso (λ _ → ¬ B) ⟩
      ⊥         ∎Iso

    ¬⊥*-Unit-Iso : Iso (¬ ⊥*) Unit
    ¬⊥*-Unit-Iso .Iso.fun = λ _ → tt
    ¬⊥*-Unit-Iso .Iso.inv = λ _ ()
    ¬⊥*-Unit-Iso .Iso.leftInv = λ { _ i () }
    ¬⊥*-Unit-Iso .Iso.rightInv = λ _ → refl

    iso₂ : Iso (¬ ⊥* × B) B
    iso₂ =
      ¬ ⊥* × B Iso⟨ Sigma.Σ-cong-iso-fst ¬⊥*-Unit-Iso ⟩
      Unit × B Iso⟨ Sigma.lUnit×Iso ⟩
      B ∎Iso

  xor-identityˡ-Equiv : ⊥* xor B ≃ B
  xor-identityˡ-Equiv = isoToEquiv xor-identityˡ-Iso

  xor-identityˡ : ⊥* xor B ≡ B
  xor-identityˡ = ua xor-identityˡ-Equiv

module _ {ℓ} (P Q : Type ℓ) where
  open Iso

  xor-comm-Iso : Iso (P xor Q) (Q xor P)
  xor-comm-Iso =
    (P × ¬ Q) ⊎ (¬ P × Q) Iso⟨ ⊎-swap-Iso ⟩
    (¬ P × Q) ⊎ (P × ¬ Q) Iso⟨ ⊎Iso Σ-swap-Iso Σ-swap-Iso ⟩
    (Q × ¬ P) ⊎ (¬ Q × P) ∎Iso

  xor-comm-Equiv : (P xor Q) ≃ (Q xor P)
  xor-comm-Equiv = isoToEquiv xor-comm-Iso

  xor-comm : P xor Q ≡ Q xor P
  xor-comm = ua xor-comm-Equiv

module _ {ℓ} (P Q R : Type ℓ) where
  open Iso

  xor-assoc-Iso : Iso (P xor (Q xor R)) ((P xor Q) xor R)
  xor-assoc-Iso =
    ((P × ¬ ((Q × ¬ R) ⊎ (¬ Q × R))) ⊎ (¬ P × ((Q × ¬ R) ⊎ (¬ Q × R)))) Iso⟨ {! !} ⟩
    ((((P × ¬ Q) ⊎ (¬ P × Q)) × ¬ R) ⊎ (¬ ((P × ¬ Q) ⊎ (¬ P × Q)) × R)) ∎Iso

  xor-assoc-Equiv : (P xor (Q xor R)) ≃ ((P xor Q) xor R)
  xor-assoc-Equiv = isoToEquiv xor-assoc-Iso

  xor-assoc : P xor (Q xor R) ≡ (P xor Q) xor R
  xor-assoc = ua xor-assoc-Equiv


-- xor-⊥*-unitˡEquiv : (A : Type ℓ) → ⊥* xor A ≃ A
-- xor-⊥*-unitˡEquiv A = {! !}

