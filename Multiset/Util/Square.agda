module Multiset.Util.Square where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
  using (isProp→SquareP)

private
  variable
    ℓ ℓ' : Level

module _
  {A : I → I → Type ℓ}
  {B : (i j : I) → A i j → Type ℓ'}
  {x₀₀ : Σ (A i0 i0) (B i0 i0)}
  {x₀₁ : Σ (A i0 i1) (B i0 i1)}
  {x₀₋ : PathP (λ j → Σ (A i0 j) (B i0 j)) x₀₀ x₀₁}
  {x₁₀ : Σ (A i1 i0) (B i1 i0)}
  {x₁₁ : Σ (A i1 i1) (B i1 i1)}
  {x₁₋ : PathP (λ j → Σ (A i1 j) (B i1 j)) x₁₀ x₁₁}
  {x₋₀ : PathP (λ i → Σ (A i i0) (B i i0)) x₀₀ x₁₀}
  {x₋₁ : PathP (λ i → Σ (A i i1) (B i i1)) x₀₁ x₁₁}
  where

  fstP : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → {x₀ : Σ (A i0) (B i0)}
    → {x₁ : Σ (A i1) (B i1)}
    → PathP (λ i → Σ (A i) (B i)) x₀ x₁
    → PathP A (fst x₀) (fst x₁)
  fstP p = λ i → fst (p i)
  {-# INLINE fstP #-}

  sndP : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
    → {x₀ : Σ (A i0) (B i0)}
    → {x₁ : Σ (A i1) (B i1)}
    → (p : PathP (λ i → Σ (A i) (B i)) x₀ x₁)
    → PathP (λ i → B i (fstP p i)) (snd x₀) (snd x₁)
  sndP p = λ i → snd (p i)
  {-# INLINE sndP #-}

  ΣSquareP :
    Σ[ sq ∈ SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁) ]
      SquareP (λ i j → B i j (sq i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  ΣSquareP sq = λ i j → (sq .fst i j) , (sq .snd i j)

  ΣSquarePProp : ((a : A i1 i1) → isProp (B i1 i1 a))
    → SquareP A (fstP x₀₋) (fstP x₁₋) (fstP x₋₀) (fstP x₋₁)
    → SquareP (λ i j → Σ (A i j) (B i j)) x₀₋ x₁₋ x₋₀ x₋₁
  fst (ΣSquarePProp propB₁₁ sqA i j) = sqA i j
  snd (ΣSquarePProp propB₁₁ sqA i j) = sqB i j where
    propB : (i j : I) → isProp (B i j (sqA i j))
    propB i j = transport (λ k → isProp (B (~ k ∨ i) (~ k ∨ j) (sqA (~ k ∨ i) (~ k ∨ j)))) (propB₁₁ (sqA i1 i1))

    sqB : SquareP (λ i j → B i j (sqA i j)) (sndP x₀₋) (sndP x₁₋) (sndP x₋₀) (sndP x₋₁)
    sqB = isProp→SquareP (λ i j → propB i j) _ _ _ _
