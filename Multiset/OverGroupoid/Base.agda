module Multiset.OverGroupoid.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
  using
    ( ua
    ; ua→
    )
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using
    ( _∘_
    )

open import Cubical.Foundations.Structure
open import Cubical.Syntax.⟨⟩

open import Cubical.Data.Unit as Unit
  using
    ( Unit
    )
open import Cubical.Data.Sigma as Σ
  using
    ( ΣPathP
    ; Σ≡Prop
    )
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    ; _+_
    )
open import Cubical.Data.FinSet as FinSet
  using
    ( FinSet
    ; isFinSet
    ; isPropIsFinSet
    )

import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ : Level
    X : Type ℓ

FinSet₀ : Type₁
FinSet₀ = FinSet ℓ-zero


FMSet : Type ℓ → Type (ℓ-max ℓ (ℓ-suc ℓ-zero))
FMSet X = Σ[ Y ∈ FinSet₀ ] (⟨ Y ⟩ → X)

FMSetPath : ∀ {V W : Type}
  → {finV : isFinSet V}
  → {finW : isFinSet W}
  → {v : V → X}
  → {w : W → X}
  → (p : V ≡ W)
  → (P : PathP (λ i → p i → X) v w)
  → Path (FMSet X) ((V , finV) , v) (((W , finW) , w))
FMSetPath p P = ΣPathP ((Σ≡Prop (λ _ → isPropIsFinSet) p) , P)

FMSetPathP≃ : ∀ {V W : Type}
  → {finV : isFinSet V}
  → {finW : isFinSet W}
  → {v : V → X}
  → {w : W → X}
  → (α : V ≃ W)
  → (eq : ∀ k → v k ≡ w (equivFun α k))
  → Path (FMSet X) ((V , finV) , v) (((W , finW) , w))
FMSetPathP≃ α eq = FMSetPath (ua α) (ua→ eq)


_∷_ : X → FMSet X → FMSet X
x ∷ ((Y , n , finY) , v) =
  ( ( Unit ⊎ Y
    , (suc n)
    , PT.map (Sum.⊎-equiv (idEquiv Unit)) finY
    )
  , Sum.elim (λ _ → x) v
  )