module Multiset.Util.Equiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
  using
    ( Iso
    ; isoToEquiv
    )

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    X : Type ℓ
    Y : Type ℓ'
    Z : Type ℓ''
    W : Type ℓ'''

open Iso

postComp≅ : (α : X ≃ Y) → Iso (Z ≃ X) (Z ≃ Y)
postComp≅ α .fun = _∙ₑ α
postComp≅ α .inv = _∙ₑ (invEquiv α)
postComp≅ {Y = Y} {Z = Z} α .rightInv = λ (β : Z ≃ Y) →
  (β ∙ₑ invEquiv α) ∙ₑ α
    ≡⟨ sym (compEquiv-assoc _ _ _) ⟩
  β ∙ₑ (invEquiv α ∙ₑ α)
    ≡⟨ cong (β ∙ₑ_) (invEquiv-is-linv _) ⟩
  β ∙ₑ idEquiv _
    ≡⟨ compEquivEquivId _ ⟩
  β
    ∎
postComp≅ {X = X} {Z = Z} α .leftInv = λ (γ : Z ≃ X) →
  (γ ∙ₑ α) ∙ₑ invEquiv α
    ≡⟨ sym (compEquiv-assoc _ _ _) ⟩
  γ ∙ₑ (α ∙ₑ invEquiv α)
    ≡⟨ cong (γ ∙ₑ_) (invEquiv-is-rinv _) ⟩
  γ ∙ₑ idEquiv _
    ≡⟨ compEquivEquivId _ ⟩
  γ
    ∎

postComp : (α : X ≃ Y) → (Z ≃ X) ≃ (Z ≃ Y)
postComp α = isoToEquiv (postComp≅ α)

postCompIdEquiv : postComp (idEquiv X) ≡ idEquiv (Z ≃ X)
postCompIdEquiv {X = X} {Z = Z} = equivEq
  ( funExt λ (γ : Z ≃ X) →
    γ ∙ₑ (idEquiv X) ≡⟨ compEquivEquivId _ ⟩ γ ∎
  )

postCompCompEquiv : ∀ (α : X ≃ Y) (β : Y ≃ W)
  → postComp {Z = Z} (α ∙ₑ β) ≡ postComp α ∙ₑ postComp β
postCompCompEquiv α β = equivEq
  ( funExt λ γ →
    γ ∙ₑ (α ∙ₑ β)
      ≡⟨ compEquiv-assoc _ _ _ ⟩
    (γ ∙ₑ α) ∙ₑ β
    ∎
  )
