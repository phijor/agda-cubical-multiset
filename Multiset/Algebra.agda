module Multiset.Algebra where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Id using (ap)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic renaming ( ⊥ to ⊥ₚ )
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base renaming
  ( rec to rec-⊎
  ; inr to inr-⊎
  ; inl to inl-⊎
  )
open import Cubical.Functions.Logic
open import Cubical.Relation.Nullary.Base using (Discrete)

open import Multiset.Base

record M-alg {ℓ : Level} : Type (ℓ-suc ℓ) where
  field
    A : Type ℓ
    εA : A
    _⊕A_ : (a b : A) → A
    unitA : (m : A)     → εA ⊕A m ≡ m
    assocA : (m n o : A) → m ⊕A n ⊕A o ≡ (m ⊕A n) ⊕A o
    commA : (m n : A)    → m ⊕A n ≡ n ⊕A m
    truncA : isSet A

  infixr 8 _⊕A_

open M-alg

record M-Dalg {ℓ : Level} {X : Type} : Type (ℓ-suc ℓ) where
  field
    Carrier : M X → Type ℓ
    Cε : Carrier ε
    _C⊕_ : {m n : M X} → Carrier m → Carrier n → Carrier (m ⊕ n)
    Cunit : {m : M X} → (x : Carrier m) → PathP (λ i → Carrier (unit m i)) (Cε C⊕ x) x
    -- continue for the rest of the path constructors

-- Recursion
rec : {ℓ : Level} {X : Type} (Alg : M-alg {ℓ})
  → (ηA : X → Alg .A)
  → M X → Alg .A
rec Alg ηA (η x) = ηA x
rec Alg ηA ε = Alg .εA
rec Alg ηA (m ⊕ n) = Alg. _⊕A_ (rec Alg ηA m) (rec Alg ηA n)
rec Alg ηA (unit m i) = Alg .unitA (rec Alg ηA m) i
rec Alg ηA (assoc m n o i) = Alg .assocA (rec Alg ηA m) (rec Alg ηA n) (rec Alg ηA o) i
rec Alg ηA (comm m n i) = Alg .commA (rec Alg ηA m) (rec Alg ηA n) i
rec Alg ηA (trunc m n eq₁ eq₂ i j) = truncA
  Alg (rec Alg ηA m) (rec Alg ηA n)
  (cong (rec Alg ηA) eq₁) (cong (rec Alg ηA) eq₂) i j

private
  variable
    ℓX : Level

hPropDep : {X : Type ℓX} (ℓ : Level) → Type (ℓ-max ℓX (ℓ-suc ℓ))
hPropDep {_} {X} ℓ = X → hProp ℓ

str-dep : {X : Type ℓX} {ℓ : Level} → (P : hPropDep {_} {X} ℓ) → (x : X) → isProp ⟨ P x ⟩
str-dep P = λ x → str (P x)

hPropDep→isPropDep : {ℓ ℓX : Level} {X : Type ℓX} → (P : hPropDep {_} {X} ℓ)
  → {x₀ x₁ : X}
  → (p₀ : ⟨ P x₀ ⟩) (p₁ : ⟨ P x₁ ⟩)
  → (p : x₀ ≡ x₁)
  → PathP (λ i → ⟨ P (p i) ⟩) p₀ p₁
hPropDep→isPropDep {X = X} P {x₀} {x₁} = isOfHLevel→isOfHLevelDep 1 {A = X} (str-dep P) {x₀} {x₁}

-- Induction principle.
--
-- Given a family `P` of properties over `M X`, we can show `P(m)` for
-- any `m ∈ M X` provided that:
-- ∙ Pη : P holds for all singleton multisets
-- ∙ Pε : P holds for the empy multiset
-- ∙ P∧ : P holds for the union of multisets if it holds for its factors
ind : {ℓ ℓX : Level} {X : Type ℓX}
  (P : M X → hProp ℓ)
  → (Pη : (x : X) → ⟨ P (η x) ⟩)
  → (Pε : ⟨ P ε ⟩)
  → (_P∧_ : {m n : M X} → ⟨ P m ⟩ → ⟨ P n ⟩ → ⟨ P (m ⊕ n) ⟩)
  → (m : M X)
  → ⟨ P m ⟩
ind P Pη Pε _P∧_ (η x) = Pη x
ind P Pη Pε _P∧_ ε = Pε
ind P Pη Pε _P∧_ (m ⊕ n) = (ind P Pη Pε _P∧_ m) P∧ (ind P Pη Pε _P∧_ n)
ind P Pη Pε _P∧_ (unit m i) =
  let Pm = ind P Pη Pε _P∧_ m in
  hPropDep→isPropDep P (Pε P∧ Pm) Pm (unit m) i
ind P Pη Pε _P∧_ (assoc m n o i) =
  let Pm = ind P Pη Pε _P∧_ m in
  let Pn = ind P Pη Pε _P∧_ n in
  let Po = ind P Pη Pε _P∧_ o in
  hPropDep→isPropDep P (Pm P∧ (Pn P∧ Po)) ((Pm P∧ Pn) P∧ Po) (assoc m n o) i
ind P Pη Pε (_P∧_) (comm m n i) =
  let Pm = ind P Pη Pε _P∧_ m in
  let Pn = ind P Pη Pε _P∧_ n in
  hPropDep→isPropDep P (Pm P∧ Pn) (Pn P∧ Pm) (comm m n) i
ind P Pη Pε (_P∧_) (trunc m n eq₀ eq₁ i j) =
  let heq = trunc m n eq₀ eq₁ in
  let P₀ = ind P Pη Pε _P∧_ (eq₀ j) in
  let P₁ = ind P Pη Pε _P∧_ (eq₁ j) in
  let P' = hPropDep→isPropDep P P₀ P₁ in
  P' {! ap ? heq  !} {!   !}
  -- {! ind P Pη Pε _P∧_ !}

M-M-alg : {X : Type} → M-alg
M-M-alg {X} = record
  { A = M X
  ; εA = ε
  ; _⊕A_ = _⊕_
  ; unitA = unit
  ; assocA = assoc
  ; commA = comm
  ; truncA = trunc
  } where open M

hProp₀ = hProp ℓ-zero
hProp₀-M-alg : M-alg {ℓ-suc ℓ-zero}
hProp₀-M-alg = record
  { A = hProp ℓ-zero
  ; εA = ⊥ₚ
  ; _⊕A_ = _⊔_
  ; unitA = ⊔-identityˡ
  ; assocA = ⊔-assoc
  ; commA = ⊔-comm
  ; truncA = isSetHProp
  }

ℕ-M-alg : M-alg
ℕ-M-alg = record
  { A = ℕ
  ; εA = 0
  ; _⊕A_ = _+_
  ; unitA = λ _ → refl
  ; assocA = +-assoc
  ; commA = +-comm
  ; truncA = isSetℕ
  }

-- Membership
_∈_ : {X : Type} → X → M X → hProp₀
x ∈ m = rec hProp₀-M-alg (λ y → x ≡ₚ y) m

infix 80 _∈_

χ : {X : Type} → (p : Discrete X) → (x y : X) → ℕ
χ p x y = if (Dec→Bool (p x y)) then 1 else 0 -- We must have decidable equality on X for this to work.

-- Multiplicity
_♯_ : {X : Type} → {p : Discrete X} → X → M X → ℕ
_♯_ {p = p} x m = rec ℕ-M-alg (χ p x) m

flatten : {X : Type} → M (M X) → M X
flatten = rec M-M-alg λ m → m

-- Size
sizeof : {X : Type} → M X → ℕ
sizeof = rec ℕ-M-alg (λ _ → 1)

sizeof-ε : {X : Type} → sizeof {X} ε ≡ 0
sizeof-ε = refl

sizeof-η : {X : Type} → {x : X} → sizeof (η x) ≡ 1
sizeof-η = refl

sizeof-⊕ : {X : Type} → {m n : M X} → sizeof (m ⊕ n) ≡ sizeof m + sizeof n
sizeof-⊕ = refl


sizeof≡0→ε : {X : Type} → (m : M X) → sizeof m ≡ 0 → m ≡ ε
sizeof≡0→ε = ind
  -- Prop
  (λ m → ((sizeof m ≡ 0 → m ≡ ε) , isPropΠ λ _ →  trunc m ε ))
  -- Pη
  (λ { _ 1≡0 → ex-falso (snotz 1≡0) })
  -- Pε
  (λ _ → refl)
  -- P∧
  (λ {m} {n} IHm IHn sz-⊕≡0 →
    let sz-m≡0 , sz-n≡0 = m+n≡0→m≡0×n≡0 {sizeof m} {sizeof n} sz-⊕≡0 in
    let m≡ε = IHm sz-m≡0 in
    let n≡ε = IHn sz-n≡0 in
    m ⊕ n
      ≡⟨ cong (_⊕ n) m≡ε ⟩
    ε ⊕ n
      ≡⟨ unit n ⟩
    n
      ≡⟨ n≡ε ⟩
    ε ∎
  )

η≢ε : {X : Type} → {x : X} → (η x ≡ ε) → Cubical.Data.Empty.⊥
η≢ε ηx≡ε = ex-falso (snotz (cong sizeof ηx≡ε))

1-split : (m n : ℕ) → Type
1-split m n = ((m ≡ 1) × (n ≡ 0)) ⊎ ((m ≡ 0) × (n ≡ 1))

+-≡1→0-or-1 : {m n : ℕ} → m + n ≡ 1 → ((m ≡ 1) × (n ≡ 0)) ⊎ ((m ≡ 0) × (n ≡ 1))
+-≡1→0-or-1 {zero} {zero} eq = ex-falso (znots eq)
+-≡1→0-or-1 {zero} {suc n} eq = inr-⊎ ( refl ,  eq )
+-≡1→0-or-1 {suc m} {zero} eq = inl-⊎ (cong suc (sym (+-zero m)) ∙ eq , refl)
+-≡1→0-or-1 {suc m} {suc n} eq =
  let suc≡0 = snd (m+n≡0→m≡0×n≡0 (injSuc eq)) in
  ex-falso (snotz suc≡0)

m+n≡1→m≡1⊎n≡1 : {m n : ℕ} → m + n ≡ 1 → (m ≡ 1) ⊎ (n ≡ 1)
m+n≡1→m≡1⊎n≡1 {zero} n≡1 = inr-⊎ n≡1
m+n≡1→m≡1⊎n≡1 {suc m} {zero} eq = inl-⊎ (
  cong suc
  let m+0≡0 = (injSuc eq) in
  let m+0≡m = +-zero m in
  (sym m+0≡m) ∙ m+0≡0)
m+n≡1→m≡1⊎n≡1 {suc m} {suc n} eq =
  let _ , suc≡0 = m+n≡0→m≡0×n≡0 (injSuc eq) in
  ex-falso (snotz suc≡0)

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

-- sizeof (η x) = 1
-- sizeof ε = 0
-- sizeof (m ⊕ n) = sizeof m + sizeof n
-- sizeof (unit m i) = unitA ℕ-M-alg (sizeof m) i
-- sizeof (assoc m n o i) = {! assocA  !}
-- sizeof (comm m m₁ i) = {!   !}
-- sizeof (trunc m m₁ x y i i₁) = {!   !}
