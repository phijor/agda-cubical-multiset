module Multiset.Prelude where

open import Cubical.Foundations.Prelude
  public

_$_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → (f : A → B)
  → (a : A)
  → B
f $ a = f a
{-# INLINE _$_ #-}

infixr -1 _$_

module PathReasoning where
  private
    variable
      ℓ : Level
      A : Type ℓ

  ≡⟨⟩∎-syntax : ∀ (x y : A) → x ≡ y → x ≡ y
  ≡⟨⟩∎-syntax _ _ p = p
  {-# INLINE ≡⟨⟩∎-syntax #-}

  syntax ≡⟨⟩∎-syntax x y p = x ≡⟨ p ⟩∎ y ∎

  private
    open import Cubical.Data.Nat.Base
    open import Cubical.Data.Nat.Properties
    idr : (n : ℕ) → n + 0 ≡ n
    idr zero = refl
    idr (suc n) =
      suc (n + 0) ≡⟨ cong suc (idr n) ⟩∎
      suc n ∎

    comm : (m n : ℕ) → m + n ≡ n + m
    comm m zero = idr m
    comm m (suc n) =
      m + suc n   ≡⟨ +-suc m n ⟩
      suc (m + n) ≡⟨ cong suc (comm m n) ⟩∎
      suc (n + m) ∎

open PathReasoning using (≡⟨⟩∎-syntax) public
