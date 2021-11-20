module Multiset.Algebra where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Logic renaming ( ⊥ to ⊥ₚ )
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat
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
