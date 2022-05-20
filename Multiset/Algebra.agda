module Multiset.Algebra where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Id using (ap)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩
open import Cubical.Functions.Logic
  hiding (¬_)
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties
  using (isPropPropTrunc)
open import Cubical.Data.Nat as ℕ
  using (ℕ)

import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary.Base
  using ( Discrete
        ; ¬_
        ; yes
        ; no
        )

open import Multiset.Base

record M-Dalg {ℓ : Level} {X : Type} : Type (ℓ-suc ℓ) where
  field
    Carrier : M X → Type ℓ
    Cε : Carrier ε
    _C⊕_ : {m n : M X} → Carrier m → Carrier n → Carrier (m ⊕ n)
    Cunit : {m : M X} → (x : Carrier m) → PathP (λ i → Carrier (unit m i)) (Cε C⊕ x) x
    -- continue for the rest of the path constructors

private
  variable
    ℓ ℓX : Level
    X : Type ℓX

⊥* : hProp ℓ
⊥* = ⊥.⊥* , λ ()

⊔*-identityˡ : (P : hProp ℓ) → _⊔_ {ℓ = ℓ} ⊥* P ≡ P
⊔*-identityˡ P =
  ⇒∶ (⊔-elim ⊥* P (λ _ → P) (λ ()) λ p → p)
  ⇐∶ inr

any : (p : X → hProp ℓ) → M X → hProp ℓ
any p = rec isSetHProp ⊥* p _⊔_ ⊔*-identityˡ ⊔-assoc ⊔-comm

all : (p : X → hProp ℓ) → M X → hProp ℓ
all p = rec isSetHProp ⊤ p _⊓_ ⊓-identityˡ ⊓-assoc ⊓-comm

count : (♯_ : X → ℕ) → M X → ℕ
count ♯_ = rec ℕ.isSetℕ 0 ♯_ ℕ._+_ (λ _ → refl) ℕ.+-assoc ℕ.+-comm

-- Membership
_∈_ : {ℓ : Level} → {X : Type ℓ} → X → M X → hProp ℓ
x ∈ m = any (x ≡ₚ_) m

infix 80 _∈_

module _ (_≡?_ : Discrete X) where
  private
    χ : (x y : X) → ℕ
    χ x y with x ≡? y
    ... | yes _ = 1
    ... | no _ = 0

  -- Multiplicity
  _♯_ : X → M X → ℕ
  _♯_ x = count (χ x)

flatten : M (M X) → M X
flatten = rec isSetM ε (λ m → m) _⊕_ unit assoc comm

-- -- Size
sizeof : M X → ℕ
sizeof = count (λ _ → 1)

sizeof-ε : sizeof {X = X} ε ≡ 0
sizeof-ε = refl

sizeof-η : {x : X} → sizeof (η x) ≡ 1
sizeof-η = refl

sizeof-⊕ : (m n : M X) → sizeof (m ⊕ n) ≡ sizeof m ℕ.+ sizeof n
sizeof-⊕ _ _ = refl


sizeof≡0→ε : (m : M X) → sizeof m ≡ 0 → m ≡ ε
sizeof≡0→ε {X = X} = ind ((λ m → isPropΠ (λ _ → isSetM m ε))) Pε Pη P+ where
  Pε : sizeof {X = X} ε ≡ 0 → ε ≡ ε
  Pε _ = refl

  Pη : (x : X) → sizeof (η x) ≡ 0 → η x ≡ ε
  Pη _ 1≡0 = ⊥.rec (ℕ.snotz 1≡0)

  P+ : {m n : M X}
      → (sizeof m ≡ 0 → m ≡ ε)
      → (sizeof n ≡ 0 → n ≡ ε)
      → sizeof (m ⊕ n) ≡ 0 → m ⊕ n ≡ ε
  P+ {m = m} {n = n} IHm IHn sz-m⊕n≡0 =
    let sz-m≡0 , sz-n≡0 = ℕ.m+n≡0→m≡0×n≡0 {sizeof m} {sizeof n} sz-m⊕n≡0 in
    m ⊕ n
      ≡⟨ cong (_⊕ n) (IHm sz-m≡0) ⟩
    ε ⊕ n
      ≡⟨ unit n ⟩
      n
      ≡⟨ IHn sz-n≡0 ⟩
    ε ∎

η≢ε : {x : X} → ¬ (η x ≡ ε)
η≢ε ηx≡ε = ⊥.rec (ℕ.snotz (cong sizeof ηx≡ε))

-- 1-split : (m n : ℕ) → Type
-- 1-split m n = ((m ≡ 1) × (n ≡ 0)) ⊎ ((m ≡ 0) × (n ≡ 1))

-- +-≡1→0-or-1 : {m n : ℕ} → m + n ≡ 1 → ((m ≡ 1) × (n ≡ 0)) ⊎ ((m ≡ 0) × (n ≡ 1))
-- +-≡1→0-or-1 {zero} {zero} eq = ex-falso (znots eq)
-- +-≡1→0-or-1 {zero} {suc n} eq = inr-⊎ ( refl ,  eq )
-- +-≡1→0-or-1 {suc m} {zero} eq = inl-⊎ (cong suc (sym (+-zero m)) ∙ eq , refl)
-- +-≡1→0-or-1 {suc m} {suc n} eq =
--   let suc≡0 = snd (m+n≡0→m≡0×n≡0 (injSuc eq)) in
--   ex-falso (snotz suc≡0)

-- m+n≡1→m≡1⊎n≡1 : {m n : ℕ} → m + n ≡ 1 → (m ≡ 1) ⊎ (n ≡ 1)
-- m+n≡1→m≡1⊎n≡1 {zero} n≡1 = inr-⊎ n≡1
-- m+n≡1→m≡1⊎n≡1 {suc m} {zero} eq = inl-⊎ (
--   cong suc
--   let m+0≡0 = (injSuc eq) in
--   let m+0≡m = +-zero m in
--   (sym m+0≡m) ∙ m+0≡0)
-- m+n≡1→m≡1⊎n≡1 {suc m} {suc n} eq =
--   let _ , suc≡0 = m+n≡0→m≡0×n≡0 (injSuc eq) in
--   ex-falso (snotz suc≡0)

-- sizeof-1→η : {X : Type} → {m : M X} → sizeof m ≡ 1 → Σ X (λ x → m ≡ η x)
-- sizeof-1→η {X} {η x} _ = x , refl
-- sizeof-1→η {X} {ε} sz-ε≡1 = ex-falso (znots ((sym sizeof-ε) ∙ sz-ε≡1))
-- sizeof-1→η {X} {m ⊕ n} sz-⊕≡1 =
--   let sz-m = sizeof-1→η {_} {m} in
--   let sz-n = sizeof-1→η {_} {n} in
--   let sz+sz≡1 : (sizeof m + sizeof n ≡ 1)
--       sz+sz≡1 = (sym sizeof-⊕) ∙ sz-⊕≡1 in
--   let h : 1-split (sizeof m) (sizeof n)
--       h = +-≡1→0-or-1 sz+sz≡1 in
--   rec-⊎ (λ ( sz-m≡1 , sz-n≡0 ) → {! let n≡ε = ? in ?  !}) {!   !} h
-- sizeof-1→η {X} {unit m i} eq = {!   !}
-- sizeof-1→η {X} {assoc m m₁ m₂ i} eq = {!   !}
-- sizeof-1→η {X} {comm m m₁ i} eq = {!   !}
-- sizeof-1→η {X} {trunc m m₁ x y i i₁} eq = {!   !}
