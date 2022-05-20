module Multiset.CyclicList.Base where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    )

infixr 5 _∷_
infixl 5 _∷ʳ_

interleaved mutual


  data C {ℓ : Level} (X : Type ℓ) : (n : ℕ) → Type (ℓ-suc ℓ)
  shift : ∀ {ℓ} {X : Type ℓ} {n} → (k : ℕ) → C X (suc n) → C X (suc n)

  data C {ℓ : Level} (X : Type ℓ) where
    []   : C X 0
    _∷_  : ∀ {n} →   X   → C X n → C X (suc n)
    _∷ʳ_ : ∀ {n} → C X n →   X   → C X (suc n)
    »_   : ∀ {n} → C X (suc n) → C X (suc n)

    cons-snoc  : ∀ {n} → (h t : X) → (xs : C X n)
      → (h ∷ xs) ∷ʳ t ≡ h ∷ (xs ∷ʳ t)
    shift-cons : ∀ {n} → (x : X) → (xs : C X n)
      → » (xs ∷ʳ x) ≡ x ∷ xs

    cycle : ∀ {n} → (xs : C X (suc n)) → shift n xs ≡ xs

    isSetC : ∀ {n} → isSet (C X n)

  shift 0 xs = xs
  shift (suc k) xs = » (shift k xs)

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

-- rec : {A : Type ℓ'}

-- isPropC0 : isProp (C X 0)
-- isPropC0 [] [] = refl
-- isPropC0 [] (isSetC ys ys₁ x y i i₁) = {!   !}
-- isPropC0 (isSetC xs xs₁ x y i i₁) ys = {!   !}

[_] : X → C X 1
[ x ] = x ∷ []

[_]ʳ : X → C X 1
[ x ]ʳ = [] ∷ʳ x

«_ : ∀ {n} → C X n → C X n
«_ {n = ℕ.zero} xs = xs
«_ {n = suc n} xs = shift n xs

-- « [] = []
-- « (x ∷ xs) = xs ∷ʳ x
-- « (xs ∷ʳ x) = {!   !}
-- « (» xs) = xs
-- « cons-snoc h t xs i = {!   !}
-- « shift-cons x xs i = {!   !}
-- « isSetC xs xs₁ x y i i₁ = {!   !}

-- length : C X → ℕ
-- length [] = 0
-- length (x ∷ xs) = suc (length xs)
-- length (xs ∷ʳ x) = suc (length xs)
-- length (» xs) = length xs
-- length (cons-snoc h t xs i) = {!   !}
-- length (shift-cons x xs i) = {!   !}
-- length (isSetC xs xs₁ x y i i₁) = {!   !}
