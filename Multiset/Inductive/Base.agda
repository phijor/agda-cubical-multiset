module Multiset.Inductive.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
  using (_∘_)
open import Cubical.Foundations.HLevels
  using
    ( isOfHLevelDep
    ; isOfHLevel→isOfHLevelDep
    ; isPropDep→isSetDep
    )

-- Finite multisets of a type, a.k.a. the free commutative monoid
-- -- As a HIT
-- -- (check Choudhury, Fiore: https://arxiv.org/abs/2110.05412)

infixr 8 _⊕_

data M {ℓ : Level} (X : Type ℓ) : Type ℓ where
-- -- point constructors
  η : (x : X) → M X          -- η = \eta
  ε : M X                     -- ε = \Ge or \epsilon
  _⊕_ : (m n : M X) → M X    -- ⊕ = \o+ or \oplus

-- -- path constructors
  unit  : (m     : M X) → ε ⊕ m ≡ m
  assoc : (m n o : M X) → m ⊕ n ⊕ o ≡ (m ⊕ n) ⊕ o
  comm  : (m n   : M X) → m ⊕ n ≡ n ⊕ m

-- -- set truncation
  trunc : isSet (M X)

unit' : {X : Type} → (m : M X) → m ⊕ ε ≡ m
unit' m = (comm m ε) ∙ (unit m)

open M

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

isSetM : isSet (M X)
isSetM = trunc

rec : {A : Type ℓ'}
  → (setA : isSet A)
  → (0̂ : A)
  → (η̂ : X → A)
  → (_+_ : (a b : A) → A)
  → (+-unit : ∀ a → 0̂ + a ≡ a)
  → (+-assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c)
  → (+-comm : ∀ a b → a + b ≡ b + a)
  → M X → A
rec {A = A} setA 0̂ η̂ _+_ +-unit +-assoc +-comm = go where
  go : _ → A
  go (η x) = η̂ x
  go ε = 0̂
  go (m ⊕ n) = (go m) + (go n)
  go (unit m i) = +-unit (go m) i
  go (assoc m n k i) = +-assoc (go m) (go n) (go k) i
  go (comm m n i) = +-comm (go m) (go n) i
  go (trunc m n p q i j) = setA (go m) (go n) (cong go p) (cong go q) i j


map : ∀ {ℓ''} {Y : Type ℓ''} → (X → Y) → M X → M Y
map f = rec trunc ε (η ∘ f) _⊕_ unit assoc comm

-- Elimination into a family of sets.
elim : {A : M X → Type ℓ'}
  → (setA : isOfHLevelDep 2 A)
  → (∅ : A ε)
  → (singleton : (x : X) → A (η x))
  → (_∪_ : {m n : M X} → A m → A n → A (m ⊕ n))
  → (∪-unit : ∀ {m} (a : A m) → PathP (λ i → A (unit m i)) (∅ ∪ a) a)
  → (∪-assoc : ∀ {m n k} (a : A m) (b : A n) (c : A k) → PathP (λ i → A (assoc m n k i)) (a ∪ (b ∪ c)) ((a ∪ b) ∪ c))
  → (∪-comm : ∀ {m n} (a : A m) (b : A n) → PathP (λ i → A (comm m n i)) (a ∪ b) (b ∪ a))
  → (m : M X) → A m
elim {X = X} {A = A} setA Ø singleton _∪_ ∪-unit ∪-assoc ∪-comm = go where
  go : (m : M X) → A m
  go (η x) = singleton x
  go ε = Ø
  go (m ⊕ n) = go m ∪ go n
  go (unit m i) = ∪-unit (go m) i
  go (assoc m n k i) = ∪-assoc (go m) (go n) (go k) i
  go (comm m n i) = ∪-comm (go m) (go n) i
  go (trunc m n p q i j) = setA (go m) (go n) (cong go p) (cong go q) (trunc m n p q) i j

-- Induction principle.
--
-- Given a family `P` of properties over `M X`, we can show `P(m)` for
-- any `m ∈ M X` provided that:
-- ∙ Pη : P holds for all singleton multisets
-- ∙ Pε : P holds for the empy multiset
-- ∙ ∨ : P holds for the union of multisets if it holds for its factors
ind : {X : Type ℓ} {P : M X → Type ℓ'}
  → (propP : ∀ m → isProp (P m))
  → (⊤ : P ε)
  → (singleton : (x : X) → P (η x))
  → (_∨_ : {m n : M X} → (p : P m) → (q : P n) → P (m ⊕ n))
  → (m : M X) → P m
ind {X = X} {P = P} propP ⊤ singleton _∨_ =
  elim (isPropDep→isSetDep propDepP) ⊤ singleton _∨_ ∨-unit ∨-assoc ∨-comm where
    propDepP : isOfHLevelDep 1 P
    propDepP = isOfHLevel→isOfHLevelDep 1 propP {a0 = _}

    ∨-unit : ∀ {m} (p : P m) →
      PathP (λ i → P (unit m i)) (⊤ ∨ p) p
    ∨-unit p = isProp→PathP (λ i → propP (unit _ i)) _ _

    ∨-assoc : {m n k : M X} (p : P m) (q : P n) (r : P k) →
      PathP (λ i → P (assoc m n k i)) (p ∨ (q ∨ r)) ((p ∨ q) ∨ r)
    ∨-assoc p q r = isProp→PathP (λ i → propP (assoc _ _ _ i)) _ _

    ∨-comm : {m n : M X} (p : P m) (q : P n) →
      PathP (λ i → P (comm m n i)) (p ∨ q) (q ∨ p)
    ∨-comm p q = isProp→PathP (λ i → propP (comm _ _ i)) _ _

_∷_ : X → M X → M X
x ∷ m = η x ⊕ m

_∷ʳ_ : M X → X → M X
m ∷ʳ x = m ⊕ η x
