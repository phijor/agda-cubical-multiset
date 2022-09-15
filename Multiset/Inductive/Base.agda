module Multiset.Inductive.Base where

open import Multiset.Prelude

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
  using (_∘_)
open import Cubical.Foundations.HLevels
  using
    ( isOfHLevelDep
    ; isOfHLevel→isOfHLevelDep
    ; isPropDep→isSetDep
    ; isSetΠ
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

unit' : ∀ {ℓ} → {X : Type ℓ} → (m : M X) → m ⊕ ε ≡ m
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
  → (setA : ∀ xs → isSet (A xs))
  → (∅ : A ε)
  → (singleton : (x : X) → A (η x))
  → (_∪_ : {m n : M X} → A m → A n → A (m ⊕ n))
  → (∪-unit : ∀ {m} (a : A m) → PathP (λ i → A (unit m i)) (∅ ∪ a) a)
  → (∪-assoc : ∀ {m n k} (a : A m) (b : A n) (c : A k) → PathP (λ i → A (assoc m n k i)) (a ∪ (b ∪ c)) ((a ∪ b) ∪ c))
  → (∪-comm : ∀ {m n} (a : A m) (b : A n) → PathP (λ i → A (comm m n i)) (a ∪ b) (b ∪ a))
  → (m : M X) → A m
elim {X = X} {A = A} setA Ø singleton _∪_ ∪-unit ∪-assoc ∪-comm = go where
  setA' : isOfHLevelDep 2 A
  setA' = isOfHLevel→isOfHLevelDep 2 setA

  go : (m : M X) → A m
  go (η x) = singleton x
  go ε = Ø
  go (m ⊕ n) = go m ∪ go n
  go (unit m i) = ∪-unit (go m) i
  go (assoc m n k i) = ∪-assoc (go m) (go n) (go k) i
  go (comm m n i) = ∪-comm (go m) (go n) i
  go (trunc m n p q i j) = setA' (go m) (go n) (cong go p) (cong go q) (trunc m n p q) i j

-- Induction principle.
--
-- Given a family `P` of properties over `M X`, we can show `P(m)` for
-- any `m ∈ M X` provided that:
-- ∙ Pη : P holds for all singleton multisets
-- ∙ Pε : P holds for the empty multiset
-- ∙ ∨ : P holds for the union of multisets if it holds for its factors
ind : {X : Type ℓ} {P : M X → Type ℓ'}
  → (propP : ∀ m → isProp (P m))
  → (⊤ : P ε)
  → (singleton : (x : X) → P (η x))
  → (_∨_ : {m n : M X} → (p : P m) → (q : P n) → P (m ⊕ n))
  → (m : M X) → P m
ind {X = X} {P = P} propP ⊤ singleton _∨_ =
  elim (λ m → isProp→isSet (propP m)) ⊤ singleton _∨_ ∨-unit ∨-assoc ∨-comm where
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

mapComp : ∀ {ℓ″ ℓ‴} {Y : Type ℓ″} {Z : Type ℓ‴}
  → ∀ {xs : M X}
  → (g : Y → Z)
  → (f : X → Y)
  → map g (map f xs) ≡ map (g ∘ f) xs
mapComp {xs = xs} g f = ind {P = λ xs → map g (map f xs) ≡ map (g ∘ f) xs} (λ xs → isSetM _ _)
  (refl {x = ε})
  (λ x → refl {x = η (g (f x))})
  (λ {xs ys} mapComp-xs mapComp-ys → cong₂ _⊕_ mapComp-xs mapComp-ys)
  xs

mapId : ∀ (xs : M X)
  → map (λ x → x) xs ≡ xs
mapId = ind (λ xs → isSetM _ _) refl (λ _ → refl) λ mapId-xs mapId-ys → cong₂ _⊕_ mapId-xs mapId-ys

-- indPath : {X : Type ℓ} {Y : Type ℓ'}
--   → {P : {xs ys : M X} → xs ≡ ys}
--   → (∀ ys → P {ε} ys)
--   → (∀ ys → P {ε} ys)
--   → (xs : M X) → ys ≡ ys'

_∷_ : X → M X → M X
x ∷ m = η x ⊕ m

infixr 7 _∷_

_∷ʳ_ : M X → X → M X
m ∷ʳ x = m ⊕ η x

∷-swap : ∀ (x y : X) xs → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
∷-swap x y xs =
  x ∷ y ∷ xs       ≡⟨⟩
  η x ⊕ (η y ⊕ xs) ≡⟨ assoc _ _ _ ⟩
  (η x ⊕ η y) ⊕ xs ≡⟨ cong (_⊕ xs) (comm _ _) ⟩
  (η y ⊕ η x) ⊕ xs ≡⟨ sym (assoc _ _ _) ⟩
  η y ⊕ (η x ⊕ xs) ≡⟨⟩
  y ∷ x ∷ xs ∎

∷-swap-split≡ : ∀ {ℓ} {X : Type ℓ} {x y : X} {xs ys zs : M X}
  → (xs ≡ y ∷ zs)
  → (x ∷ zs ≡ ys)
  → x ∷ xs ≡ y ∷ ys
∷-swap-split≡ {x = x} {y} {xs} {ys} {zs} xs-split ys-split =
  x ∷ xs ≡⟨ cong (x ∷_) xs-split ⟩
  x ∷ y ∷ zs ≡⟨ ∷-swap x y zs ⟩
  y ∷ x ∷ zs ≡⟨ cong (y ∷_) ys-split ⟩
  y ∷ ys ∎

_++_ : M X → M X → M X
_++_ {X = X} = rec {A = M X → M X} (isSetΠ (λ ys → isSetM)) (λ ys → ys) _∷_ (λ xs++_ ys++_ → xs++_ ∘ ys++_) unit* assoc* comm*
  where
    unit* : ∀ (xs++_) → (λ ys → xs++ ys) ≡ xs++_
    unit* _ = refl

    assoc* : ∀ xs++_ ys++_ zs++_ → _
    assoc* _ _ _ = refl

    comm* : ∀ xs++_ ys++_ → (xs++_ ∘ ys++_) ≡ (ys++_ ∘ xs++_)
    comm* xs++_ ys++_ = funExt $ ind (λ zs → isSetM _ _) {! !} {! !} {! !}
  
∷-elim : {B : M X → Type ℓ'}
  → (setB : ∀ m → isSet (B m))
  → (nil : B ε)
  → (cons : (x : X) → {xs : M X} → B xs → B (x ∷ xs))
  → (swap : (x y : X) → {xs : M X} → {b : B xs} → PathP (λ i → B (∷-swap x y xs i)) (cons x (cons y b)) (cons y (cons x b)))
  → (xs : M X) → B xs
∷-elim {B = B} setB nil cons swap = elim setB nil η* {! !} {! !} {! !} {! !} where
  η* : ∀ x → B (η x)
  η* x = subst B (unit' (η x)) (cons x nil)

  _⊕*_ : ∀ {xs ys} → B xs → B ys → B (xs ⊕ ys)
  b-xs ⊕* b-ys = {! !}

module _ where
  open import Cubical.Data.Nat as ℕ using (ℕ)

  count : (♯_ : X → ℕ) → M X → ℕ
  count ♯_ = rec ℕ.isSetℕ 0 ♯_ ℕ._+_ (λ _ → refl) ℕ.+-assoc ℕ.+-comm
