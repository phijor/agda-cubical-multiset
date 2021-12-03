module Multiset.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

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

map : {X Y : Type} → (X → Y) → M X → M Y
map f (η x) = η (f x)
map f ε = ε
map f (m ⊕ n) = map f m ⊕ map f n
map f (unit m i) = unit (map f m) i
map f (assoc m n o i) = assoc (map f m) (map f n) (map f o) i
map f (comm m n i) = comm (map f m) (map f n) i
map f (trunc m n eq₁ eq₂ i j) =
  trunc (map f m) (map f n) (cong (map f) eq₁) (cong (map f) eq₂) i j
