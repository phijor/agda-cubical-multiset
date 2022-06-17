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
    ; ∃-syntax
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
open import Cubical.HITs.PropositionalTruncation as PT
  using
    ( ∣_∣₁
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

isSetSymmQuot : ∀ {n} → isSet ((Fin n → X) /₂ SymmetricAction n)
isSetSymmQuot = squash/₂

isSetFMSet : isSet (FMSet X)
isSetFMSet = isSetΣ ℕ.isSetℕ (λ _ → isSetSymmQuot)

FMSetPath : ∀ {n}
  → (v w : Fin n → X)
  → (∃[ σ ∈ (Fin n ≃ Fin n) ] PathP (λ i → (ua σ i → X)) v w)
  → Path (FMSet X) (n , [ v ]₂) (n , [ w ]₂)
FMSetPath v w = PT.elim (λ _ → isSetFMSet _ _)
  λ (σ , p) → ΣPathP (refl , (eq/₂ v w ∣ σ , p ∣₁))

map : ∀ {ℓy} {Y : Type ℓy} → (f : X → Y) → FMSet X → FMSet Y
map f (n , v) =
  ( n
  , ( SQ.rec
    isSetSymmQuot
    ([_]₂ ∘ (f ∘_))
    (λ v w → PT.elim (λ _ → isSetSymmQuot _ _) λ (σ , p) → eq/₂ _ _ ∣ σ , (ua→cong f p) ∣₁)
    v
    )
  )

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
    []∷-well-defined {x = x} v w v∼w = eq/₂ (x ∷ᶠ v) (x ∷ᶠ w) rel
      where
        rel : SymmetricAction (suc n) (x ∷ᶠ v) (x ∷ᶠ w)
        rel = PT.map (λ (σ , p) → (fsuc≃ σ) , (ua→ (Sum.elim (λ (_ : Unit) → refl) (ua→⁻ p)))) v∼w

_∷_ : X → FMSet X → FMSet X
_∷_ {X = X} x (n , [v]) = (suc n) , x∷v where
  x∷v : (Fin (suc n) → X) /₂ SymmetricAction (suc n)
  x∷v = SQ.elim (λ _ → isSetSymmQuot {n = suc n}) [ x ]∷_ []∷-well-defined [v]

infixr 5 _∷_

∷-comm : ∀ x y → (xs : FMSet X)
  → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
∷-comm {X = X} x y (n , v) = SQ.elimProp
  {P = λ [v] → x ∷ y ∷ (n , [v]) ≡ y ∷ x ∷ (n , [v])}
  (λ _ → isSetFMSet _ _)
  (λ v → FMSetPath _ _ ∣ swap₀₁ , (ua→ (comm v)) ∣₁)
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
      (λ _ → isSetSymmQuot _ _)
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
    (λ v → cons (v fzero) (go (n , {! [ v ∘ fsuc ]₂ !})))
    (λ v w v∼w → {!   !})
    v
