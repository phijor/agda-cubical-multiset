module Multiset.OverSet.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
  using
    ( _∘_
    )
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Unit as ⊤
  using
    ( Unit
    )

open import Cubical.Data.Empty as Empty
  using
    ( ⊥
    )
open import Cubical.Data.Nat as ℕ
  using
    ( ℕ
    ; suc
    ; _+_
    )
open import Cubical.Data.Sum as Sum
  using
    ( _⊎_
    )
open import Cubical.Data.Sigma as Sigma
  using
    ( ΣPathP
    )
open import Cubical.Data.SumFin as Fin
  using
    ( Fin
    ; fsuc
    ; fzero
    )

open import Cubical.HITs.SetQuotients as SQ
  renaming
    ( _/_ to _/₂_
    ; eq/ to eq/₂
    ; [_] to [_]₂
    ; squash/ to squash/₂
    )

open import Multiset.Util
  using
    ( ua→cong
    ; Π⊥≡elim
    )
open import Multiset.OverSet.Base

private
  variable
    ℓ ℓ' : Level
    X : Type ℓ

private
  isSetSetQuotient : {R : X → X → Type ℓ'} → isSet (X /₂ R)
  isSetSetQuotient = squash/₂

isSetFMSet : isSet (FMSet X)
isSetFMSet = isSetΣ ℕ.isSetℕ (λ _ → isSetSetQuotient)

map : ∀ {ℓy} {Y : Type ℓy} → (f : X → Y) → FMSet X → FMSet Y
map f (n , v) = n , (SQ.rec isSetSetQuotient ([_]₂ ∘ (f ∘_)) (λ v w (σ , p) → eq/₂ _ _ (σ , (ua→cong f p))) v)

[] : FMSet X
[] = 0 , [ Empty.elim ]₂

private
  _∷ᶠ_ : ∀ {n} → (x : X) → (xs : Fin n → X) → Fin (suc n) → X
  x ∷ᶠ xs = Sum.rec (λ _ → x) xs

  fsuc≃ : ∀ {n} → Fin n ≃ Fin n → Fin (suc n) ≃ Fin (suc n)
  fsuc≃ σ = Sum.⊎-equiv (idEquiv Unit) σ

  infixr 5 _∷ᶠ_

  module _ {n : ℕ} where
    [_]∷_ : (x : X) → (v : Fin n → X) → (Fin (suc n) → X) /₂ SymmetricAction (suc n)
    [ x ]∷ v = [ x ∷ᶠ v ]₂

    []∷-well-defined : {x : X} → (v w : Fin n → X) → (v ∼ w) → [ x ]∷ v ≡ [ x ]∷ w
    []∷-well-defined {x = x} v w (σ , p) = eq/₂ (x ∷ᶠ v) (x ∷ᶠ w) ((fsuc≃ σ) , ua→ (Sum.elim (λ _ → refl) (ua→⁻ p)))

_∷_ : X → FMSet X → FMSet X
_∷_ {X = X} x (n , [v]) = (suc n) , x∷v where
  x∷v : (Fin (suc n) → X) /₂ SymmetricAction (suc n)
  x∷v = SQ.elim (λ _ → isSetSetQuotient) [ x ]∷_ []∷-well-defined [v]

infixr 5 _∷_

∷-comm : ∀ x y → (xs : FMSet X)
  → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
∷-comm {X = X} x y (n , v) = SQ.elimProp
  {P = λ [v] → x ∷ y ∷ (n , [v]) ≡ y ∷ x ∷ (n , [v])}
  (λ _ → isSetFMSet _ _)
  (λ v → FMSetPath _ _ swap₀₁ (ua→ (comm v)))
  v
  where
    open Sum

    swap₀₁ : (Fin (2 + n)) ≃ (Fin (2 + n))
    swap₀₁ = invEquiv ⊎-assoc-≃ ∙ₑ ⊎-equiv ⊎-swap-≃ (idEquiv (Fin n)) ∙ₑ ⊎-assoc-≃

    module _ (v : Fin n → X) where
      comm : (k : Fin (2 + n))
        → (x ∷ᶠ y ∷ᶠ v) k ≡ (y ∷ᶠ x ∷ᶠ v) ((equivFun swap₀₁) k)
      comm (inl x) = refl
      comm (fsuc (inl x)) = refl
      comm (fsuc (fsuc x)) = refl

isContrFMSet₀ : ([v] : (Fin 0 → X) /₂ SymmetricAction 0) → [] ≡ (0 , [v])
isContrFMSet₀ [v] = ΣPathP
  ( refl
  , ( SQ.elimProp {P = λ [v] → [ Empty.elim ]₂ ≡ [v]}
      (λ _ → isSetSetQuotient _ _)
      (λ v → cong [_]₂ (Π⊥≡elim v))
      [v]
    )
  )

∷-elim : {B : FMSet X → Type ℓ'}
  → (setB : ∀ m → isSet (B m))
  → (nil : B [])
  → (cons : (x : X) → {xs : FMSet X} → B xs → B (x ∷ xs))
  → (comm : (x y : X) → {xs : FMSet X} → {b : B xs} → PathP (λ i → B (∷-comm x y xs i)) (cons x (cons y b)) (cons y (cons x b)))
  → (m : FMSet X) → B m
∷-elim {X = X} {B = B} setB nil cons comm = go where
  go : (m : FMSet X) → B m
  go (0     , v) = subst B (isContrFMSet₀ v) nil
  go (suc n , v) = SQ.elim {P = λ [v] → B (suc n , [v])}
    (λ m → setB (suc n , m))
    (λ v → let x = v fzero in let v' = v ∘ fsuc in subst B {!   !} (cons x {!   !}))
    {!   !}
    v
