-- Define the finite multiset functor M (HITs)
-- Define the ω-chain 1 <- M 1 <- M (M 1) <- ...
-- Construct the limit L
-- Prove that L is the final coalgebra of M
-- Look at other ways of constructing the final coalgebra (coinductive types)

module Multiset where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything hiding (assoc)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Functions.Logic renaming ( ⊥ to ⊥ₚ )
open import Cubical.Relation.Nullary


-- Finite multisets of a type, a.k.a. the free commutative monoid
-- -- As a HIT
-- -- (check Choudhury, Fiore: https://arxiv.org/abs/2110.05412)

infixr 8 _⊕_

data M (X : Type) : Type where
-- -- point constructors
  η : (x : X) → M X          -- η = \eta
  ε : M X                     -- ε = \Ge or \epsilon
  _⊕_ : (m n : M X) → M X    -- ⊕ = \o+ or \oplus

-- -- path constructors
  unit : (m : M X)     → ε ⊕ m ≡ m
  assoc : (m n o : M X) → m ⊕ n ⊕ o ≡ (m ⊕ n) ⊕ o
  comm : (m n : M X)    → m ⊕ n ≡ n ⊕ m

-- -- set truncation
  trunc : isSet (M X)


-- Another way of doing this

module Aside where

  record Finite : Type₁ where
    field
      N : Type
      size : ℕ
      equiv : ∥ N ≃ Fin size ∥

  -- Finite : Type₁
  -- Finite = Σ Type λ X → (Σ ℕ λ n → ∥ X ≃ Fin n ∥)
-- -- ∥-∥ says "forget the information inside"

  open Finite

  M' : Type → Type₁
  M' X = Σ Finite λ B → B .N → X

-- Problems:

-- -- Type₁, we cannot do ω-chains

-- -- It is not a set:
-- -- -- Given (X , n , p), (Y , m , q) and eq, eq' : (X , n , p) ≡ (Y , m , q),
-- -- -- try to prove eq = eq'. Not possible since not all n-permutations are equal

  -- isSet-Finite : isSet Finite
  -- isSet-Finite = {!   !}

  -- isSet-M' : (X : Type) → isSet (M' X)
  -- isSet-M' X = isSetΣ isSet-Finite {!   !}
  -- isSet-M' X M N = λ eq eq' → {!   !}

-- -- There is no way of fixing this, in the sense that you cannot add
-- -- finite number of coherences to get out a set

-- -- Check also: Buchholtz'21
-- -- https://www2.mathematik.tu-darmstadt.de/~buchholtz/pairs.pdf

-- Action on maps
mapM : {X Y : Type} (f : X → Y) → M X → M Y
mapM f (η x) = η (f x)
mapM f ε = ε
mapM f (m ⊕ n) = mapM f m ⊕ mapM f n
mapM f (unit m i) = unit (mapM f m) i
mapM f (assoc m n o i) = assoc (mapM f m) (mapM f n) (mapM f o) i
mapM f (comm m n i) = comm (mapM f m) (mapM f n) i
mapM f (trunc m n eq eq' i j) =
  trunc (mapM f m) (mapM f n) (cong (mapM f) eq) (cong (mapM f) eq') i j

hProp₀ = hProp ℓ-zero

infix 80 _∈_

-- M-algebra

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

hProp₀-M-alg : M-alg
hProp₀-M-alg = record
  { A = hProp₀
  ; εA = ⊥ₚ
  ; _⊕A_ = _⊔_
  ; unitA = ⊔-identityˡ
  ; assocA = ⊔-assoc
  ; commA = ⊔-comm
  ; truncA = isSetHProp
  }

+-zero' : (m : ℕ) → 0 + m ≡ m
+-zero' m = refl

ℕ-M-alg : M-alg
ℕ-M-alg = record
  { A = ℕ
  ; εA = 0
  ; _⊕A_ = _+_
  ; unitA = +-zero'
  ; assocA = +-assoc
  ; commA = +-comm
  ; truncA = isSetℕ
  }


-- Recursion
recM : {ℓ : Level} {X : Type} (Alg : M-alg {ℓ})
  → (ηA : X → Alg .A)
  → M X → Alg .A
recM Alg ηA (η x) = ηA x
recM Alg ηA ε = Alg .εA
recM Alg ηA (m ⊕ n) = Alg. _⊕A_ (recM Alg ηA m) (recM Alg ηA n)
recM Alg ηA (unit m i) = Alg .unitA (recM Alg ηA m) i
recM Alg ηA (assoc m n o i) = Alg .assocA (recM Alg ηA m) (recM Alg ηA n) (recM Alg ηA o) i
recM Alg ηA (comm m n i) = Alg .commA (recM Alg ηA m) (recM Alg ηA n) i
recM Alg ηA (trunc m n eq₁ eq₂ i j) = truncA
  Alg (recM Alg ηA m) (recM Alg ηA n)
  (cong (recM Alg ηA) eq₁) (cong (recM Alg ηA) eq₂) i j


-- Membership
_∈_ : {X : Type} → X → M X → hProp₀
x ∈ m = recM hProp₀-M-alg (λ y → x ≡ₚ y) m

χ : {X : Type} → (x y : X) → ℕ
χ x y = {!   !} -- We must have decidable equality on X for this to work.

-- Multiplicity
_♯_ : {X : Type} → X → M X → ℕ
x ♯ m = recM ℕ-M-alg (χ x) m

--==========================================

iterM : ℕ → Type → Type
iterM zero X = X
iterM (suc n) X = M (iterM n X)

iter! : (n : ℕ) → iterM (suc n) Unit → iterM n Unit
iter! zero x = tt
iter! (suc n) x = mapM (iter! n) x

record ωCone : Type₁ where
  field
    Apex : Type
    leg : (n : ℕ) → Apex → iterM n Unit
    restr : (n : ℕ) (v : Apex) → iter! n (leg (suc n) v) ≡ leg n v

-- TODO: definition of ωCone morphisms as a record

L : Type
L = Σ ((n : ℕ) → iterM n Unit) λ v →
          (n : ℕ) → iter! n (v (suc n)) ≡ v n

Lim : ωCone
Lim = record
  { Apex = L
  ; leg = λ n vr → vr .fst n
  ; restr = λ n vr → vr .snd n
  }

open ωCone

Lim-up-∃ : (V : ωCone) → V .Apex → L
Lim-up-∃ V x =
  (λ n → V .leg n x) ,
  λ n → V .restr n x

Lim-up-! : (V : ωCone) (f : V .Apex → L)
  → {!f is a ωCone morphism!}
  → f ≡ Lim-up-∃ V
Lim-up-! = {!   !}

