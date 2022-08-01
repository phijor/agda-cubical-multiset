module Multiset.Util where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence using (ua)

open import Cubical.Data.Empty as Empty using (⊥)

private
  variable
    ℓ : Level
    A : Type ℓ


ua→cong : ∀ {ℓ ℓ' ℓ''} {A₀ A₁ : Type ℓ} {e : A₀ ≃ A₁}
  {B : (i : I) → Type ℓ'}
  {C : (i : I) → Type ℓ''}
  {f₀ : A₀ → B i0} {f₁ : A₁ → B i1}
  (F : {i : I} → B i → C i)
  (p : PathP (λ i → ua e i → B i) f₀ f₁)
  → PathP (λ i → ua e i → C i) (F {i0} ∘ f₀) (F {i1} ∘ f₁)
ua→cong F p = λ i x → F (p i x)

ua→PathP : ∀ {ℓ'} {A₀ A₁ : Type ℓ} {X : Type ℓ'}
  → (e : A₀ ≃ A₁)
  → (f₀ : A₀ → X)
  → (f₁ : A₁ → X)
  → Type _
ua→PathP {X = X} e f₀ f₁ = PathP (λ i → ua e i → X) f₀ f₁

module _ {ℓ' : Level} {Y : ⊥ → Type ℓ'} where
  isPropΠ⊥ : isProp ((k : ⊥) → Y k)
  isPropΠ⊥ = isContr→isProp Empty.isContrΠ⊥

  Π⊥≡elim : (v : (k : ⊥) → Y k) → Empty.elim ≡ v
  Π⊥≡elim v _ ()

the-syntax : (A : Type ℓ) → (a : A) → A
the-syntax _ a = a

infix 0 the-syntax

syntax the-syntax A a = a ∶ A
