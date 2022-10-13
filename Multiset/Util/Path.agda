{-# OPTIONS --safe #-}

module Multiset.Util.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport
  using
    ( subst⁻
    ; transport⁻
    ; transport⁻-fillerExt
    ; transport⁻-filler
    )
open import Cubical.Functions.FunExtEquiv
  using
    ( funExtDep
    )

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : A → Type ℓ'
    x y z : A

-- Path composition, but using dependent path composition
-- over a constant type family.
compPathOver : {B : Type ℓ'} {x' y' z' : B}
  → (p : x ≡ y) (q : y ≡ z)
  → (P : Path B x' y') (Q : Path B y' z')
  → Path B x' z'
compPathOver {B = B} p q = compPathP' {B = λ _ → B} {p = p} {q = q}

[_∙_/_∙_] : {B : Type ℓ'} {x' y' z' : B}
  → (P : Path B x' y') (Q : Path B y' z')
  → (p : x ≡ y) (q : y ≡ z)
  → Path B x' z'
[ P ∙ Q / p ∙ q ] = compPathOver p q P Q

-- Dependent path composition over a *constant* family is (propositionally)
-- the same as non-dependent composition.
compPathOver≡comp : ∀ {B : Type ℓ'} {x' y' z' : B}
  → (p : Path A x y) → (q : Path A y z)
  → (P : Path B x' y') → (Q : Path B y' z')
  → compPathOver p q P Q ≡ P ∙ Q
compPathOver≡comp {B = B} p q P Q i =
  compPath-unique refl P Q
    (compPathP' {B = λ _ → B} {p = p} {q = q} P Q , compPathP'-filler {B = λ _ → B} {p = p} {q = q} P Q)
    ((P ∙ Q) , (compPath-filler P Q))
    i .fst

subst⁻-filler : (B : A → Type ℓ') (p : x ≡ y) (b : B y)
  → PathP (λ i → B (p (~ i))) b (subst⁻ B p b)
subst⁻-filler B p = transport⁻-filler (cong B p)

transportDomain : {A₀ A₁ : Type ℓ} {B : Type ℓ'}
  → {p : A₀ ≡ A₁}
  → (f : A₁ → B)
  → PathP (λ i → p i → B) (λ a₀ → f (transport p a₀)) f
transportDomain f = funExtDep λ p' → cong f (fromPathP p')

transport⁻Domain : {A₀ A₁ : Type ℓ} {B : Type ℓ'}
  → {p : A₀ ≡ A₁}
  → (f : A₀ → B)
  → PathP (λ i → p i → B) f (λ a₁ → f (transport⁻ p a₁))
transport⁻Domain f = funExtDep λ p' → cong f (fromPathP⁻ p')

infixr 4 [_∣_≡_]

[_∣_≡_] : ∀ {ℓ} → (A : Type ℓ) → (x y : A) → Type ℓ
[ A ∣ x ≡ y ] = x ≡ y

substDomain : ∀ {ℓ''} {C : Type ℓ''}
  → {x₀ x₁ : A}
  → (f : B x₀ → C)
  → (p : x₀ ≡ x₁)
  → subst (λ x → B x → C) p f ≡ λ x → f (subst⁻ B p x)
substDomain {B = B} {C = C} f p = funExt λ x₁ → transportRefl {A = C} (f (subst⁻ B p x₁))

subst⁻Domain : ∀ {ℓ''} {C : Type ℓ''}
  → {x₀ x₁ : A}
  → (f : B x₁ → C)
  → (p : x₀ ≡ x₁)
  → subst⁻ (λ x → B x → C) p f ≡ λ x → f (subst B p x)
subst⁻Domain {B = B} {C = C} f p = funExt λ x₁ → transportRefl {A = C} (f (subst B p x₁))
