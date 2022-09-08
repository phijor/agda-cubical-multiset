module Multiset.Util where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence using (ua)

open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Unit as Unit using (Unit ; tt)
open import Cubical.Data.Sigma as Sigma using (_×_)

private
  variable
    ℓ : Level
    A : Type ℓ


Path→cong : ∀ {ℓ ℓ' ℓ''} {A : (i : I) → Type ℓ}
  {B : (i : I) → Type ℓ'}
  {C : (i : I) → Type ℓ''}
  {f₀ : A i0 → B i0} {f₁ : A i1 → B i1}
  (F : {i : I} → B i → C i)
  (p : PathP (λ i → A i → B i) f₀ f₁)
  → PathP (λ i → A i → C i) (F {i0} ∘ f₀) (F {i1} ∘ f₁)
Path→cong F p = λ i x → F (p i x)

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

!_ : A → Unit
! a = tt

infixr 80 !_

